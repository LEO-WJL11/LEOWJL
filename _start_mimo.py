# -*- coding: utf-8 -*-
r"""一键启动：Lion Code 后端 + MiMo 兼容接口层（界面已删除，走浏览器）。

两段式（顺序不能反）：

    ① main.py --backend-only        我们的 Python 后端（能力都在这；界面 = /platform 网页）
    ② mimo适配.py                   MiMo 形状的兼容接口层（保留备用，界面不依赖它）

【tui/ 已整体删除】按用户指令不再拉任何终端 UI —— main.py 裸跑就是直接起后端，
界面就是浏览器里的 /platform 平台页。原段三（bun + OpenTUI 拉起）连同它的崩溃
诊断（_frontend_crashed / opentui.dll 报告）一并移除。

【看门狗】① ② 死掉会自动拉起 —— 这条是踩出来的：用户有一次盯着界面等了 10 分钟
"它啥也没干"，查下来是**后端与适配层的 python 进程一个都不在了**。本脚本常驻
等 Ctrl+C；收尾先停看门狗再收服务（顺序反了会被看门狗把刚停的又拉起来）。
"""
from __future__ import annotations

import os
import subprocess
import sys
import threading
import time
import urllib.request

ROOT = os.path.dirname(os.path.abspath(__file__))
PY = os.path.join(ROOT, ".venv", "Scripts", "python.exe")
if not os.path.isfile(PY):
    PY = sys.executable

def _env_port(name: str, default: int) -> int:
    """读环境变量里的端口；**非法值显式告警并回退默认值**，绝不让 import 崩。

    【为什么不直接 `int(...)`】这两个值完全来自外部 shell 环境（全仓库只有本文件
    读它、没有任何脚本设置它），用户手误设成 `LION_CODE_BACKEND_PORT=18080a`
    就会在 **模块导入期**抛 ValueError —— 此时 `_LOGDIR` 还没建、**一行日志都打不出来**
    ✗（本会话反复抓的"失败仍报成功 / 静默失败"的同一类形态 ✓）。
    """
    raw = os.environ.get(name)
    if raw is None or not str(raw).strip():
        return default
    try:
        return int(str(raw).strip())
    except ValueError:
        print(f"[警告] 环境变量 {name}={raw!r} 不是整数，改用默认值 {default}", flush=True)
        return default


BACKEND_PORT = _env_port("LION_CODE_BACKEND_PORT", 18080)
ADAPTER_PORT = _env_port("LION_CODE_ADAPTER_PORT", 8791)

#: 看门狗节奏：12 秒一轮（够快，又不至于抖）。连挂多次后退避到 60 秒 ——
#: 端口被占、依赖缺失这类问题重启一百次也没用，退避能避免把日志刷爆。
WATCH_INTERVAL = 12.0
WATCH_BACKOFF_AFTER = 3          # 连续挂几次开始退避
WATCH_BACKOFF_INTERVAL = 60.0

try:
    # 【必须兜底】main.py 对同款调用也包了 try/except —— 某些环境里 stdout 没有
    # reconfigure（重定向到管道/被宿主接管时会 AttributeError），裸调会 import 期崩。
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
except Exception:                                          # noqa: BLE001
    pass

def _detect_data_dir() -> str:
    """可写的运行数据根（日志 / 工作区 / MiMo home 都放它下面）。

    【为什么不能写死 `ROOT/.lbcheck`】打包安装到 `Program Files` 这类只读位置时，
    `os.makedirs(ROOT/.lbcheck)` 直接抛 PermissionError → **启动器第一句就崩** ✗
    （本会话反复吃过"静默失败"的亏，所以这里必须**显式探测 + 回退**）。
    回退到 `%LOCALAPPDATA%\\LionCode\\data` —— 那里任何用户都可写 ✓
    （真正持久化的 `~/.lioncode` 本来就在家目录，与安装位置无关 ✓）。
    """
    cand = os.path.join(ROOT, ".lbcheck")
    try:
        os.makedirs(cand, exist_ok=True)
        probe = os.path.join(cand, ".wprobe")
        with open(probe, "w", encoding="utf-8") as f:
            f.write("ok")
        os.remove(probe)
        return cand
    except OSError:
        fb = os.path.join(os.environ.get("LOCALAPPDATA") or os.path.expanduser("~"),
                          "LionCode", "data")
        os.makedirs(fb, exist_ok=True)
        return fb


_LOGDIR = _detect_data_dir()


def log(msg: str) -> None:
    """控制台 + 看门狗日志各写一份。

    【为什么要落盘】用户看不到控制台滚动的内容（TUI 占屏），事后要能查
    "什么时候重启过、重启了几次" —— 本会话反复吃过"静默失败"的亏 ✗。
    """
    line = f"[{time.strftime('%H:%M:%S')}] {msg}"
    print(line, flush=True)
    try:
        with open(os.path.join(_LOGDIR, "watchdog.log"), "a",
                  encoding="utf-8", errors="replace") as f:
            f.write(line + "\n")
    except Exception:                                     # noqa: BLE001
        pass


def wait_up(url: str, timeout: float = 60.0, proc=None, stop=None) -> bool:
    """等服务开始监听。

    【`stop` 参数是干什么的】看门狗 `shutdown()` 之后，在途的 `wait_ready` 必须尽快
    让出 —— 否则"重启窗口内新拉起的进程无人回收" ✗ 会留下孤儿 backend/adapter，
    并污染下一轮健康检查（本会话 audit2 实测的那条 MEDIUM ✓）。
    """
    end = time.time() + timeout
    while time.time() < end:
        if stop is not None and stop.is_set():
            return False
        if proc is not None and proc.poll() is not None:
            return False
        try:
            with urllib.request.urlopen(url, timeout=2):
                return True
        except Exception:                                 # noqa: BLE001
            time.sleep(0.3)
    return False


# ── 两个服务的启动命令（看门狗重启时要用同一份 ✗ 不许各写一遍 ✓）───────────
def backend_cmd(workspace_root: str) -> list[str]:
    args = ["--backend-only",
            f"--server.port={BACKEND_PORT}",
            # 【--app-root 不能少】它决定去哪找 `runtime-vulkan/llama-server.exe`
            # 和 `*.gguf`。不给的话默认是 <仓库>\python（老布局），模型会被判为
            # "未安装"从而触发重新下载，本地模型永远起不来。
            f"--app-root={ROOT}",
            # 【工作区根目录】默认是 `~/lion-code-workspace`（照 Java 的
            # application.yml）。但那个目录下 `.lioncode/` 子目录的 ACL 受限，
            # 后端存会话元数据 / 事件会吃 Permission denied（实测日志里就是它），
            # 于是会话历史没法落盘。指到仓库内（已被 .gitignore 覆盖）。
            "--lion.workspace.default-path=" + workspace_root,
            "--config-dir=" + os.path.join(_LOGDIR, "mimo")]
    # 【打包版走 exe】Nuitka 编译分发时机器上没有 Python 解释器 ✗ ——
    # 同目录若有 `LionCode.exe` 就用它（开发期没这个文件，仍走 main.py ✓）。
    exe = os.path.join(ROOT, "LionCode.exe")
    if os.path.isfile(exe):
        return [exe] + args
    return [PY, os.path.join(ROOT, "main.py")] + args


def adapter_cmd(workspace_root: str) -> list[str]:
    args = [f"--port={ADAPTER_PORT}",
            f"--backend=http://127.0.0.1:{BACKEND_PORT}",
            f"--directory={os.getcwd()}",
            # 【必须和后端同一个值】适配层要用它去 <root>/.lioncode/conversations/
            # 读历史，侧边栏切换会话时才能回放出对话内容。
            f"--workspace={workspace_root}"]
    exe = os.path.join(ROOT, "adapter.exe")
    if os.path.isfile(exe):
        return [exe] + args
    return [PY, os.path.join(ROOT, "mimo适配.py")] + args


class Watchdog(threading.Thread):
    """盯着 ① ② 还在不在，死了就拉起来。

    【边界】只管自己拉起的两个进程 ✗ ——
      · llama-server 归后端自己管（它有 `POST /api/runtime/local/start` ✓）
      · MiMo 前端归用户（他自己关窗口是正常行为 ✓ 拉起反而吓人 ✗）
    """

    def __init__(self, workspace_root: str, backend_log, adapter_log):
        super().__init__(daemon=True, name="watchdog")
        self.workspace_root = workspace_root
        self.backend_log = backend_log
        self.adapter_log = adapter_log
        self.procs: dict[str, subprocess.Popen] = {}
        self.fails = {"backend": 0, "adapter": 0}
        self.restarts = {"backend": 0, "adapter": 0}
        self.stop_event = threading.Event()

    # -- 启动
    def _env(self) -> dict[str, str]:
        """子进程环境：与**前端同一套临时目录口径**。

        【为什么 backend/adapter 也要】`TMP/TEMP/TMPDIR/SQLITE_TMPDIR` 原来只注入给
        前端子进程（main() 里那份 env ✓），两个服务的临时文件会回退到系统 `%TEMP%`。
        本机实测过"工作区外的 temp 不可写"这类问题（cl 的 `_CL_*` Permission denied、
        link 的 `lnk*.tmp` LNK1104 都是同源 ✓）—— 三段统一用 `_LOGDIR/tmp` 才一致 ✓。
        """
        tmp = os.path.join(_LOGDIR, "tmp")
        try:
            os.makedirs(tmp, exist_ok=True)
        except OSError:
            pass
        env = dict(os.environ)
        for k in ("TMP", "TEMP", "TMPDIR", "SQLITE_TMPDIR"):
            env[k] = tmp
        return env

    def spawn(self, which: str) -> subprocess.Popen:
        env = self._env()
        if which == "backend":
            p = subprocess.Popen(backend_cmd(self.workspace_root), cwd=ROOT,
                                 stdout=self.backend_log, stderr=self.backend_log,
                                 env=env)
        else:
            p = subprocess.Popen(adapter_cmd(self.workspace_root), cwd=ROOT,
                                 stdout=self.adapter_log, stderr=self.adapter_log,
                                 env=env)
        self.procs[which] = p
        return p

    def wait_ready(self, which: str, proc: subprocess.Popen, timeout: float) -> bool:
        url = (f"http://127.0.0.1:{BACKEND_PORT}/health" if which == "backend"
               else f"http://127.0.0.1:{ADAPTER_PORT}/global/health")
        # 传 stop：shutdown() 之后在途的等待要能被打断（见 wait_up 的说明）
        return wait_up(url, timeout, proc, self.stop_event)

    # -- 一轮检查
    def check_once(self) -> None:
        for which in ("backend", "adapter"):
            proc = self.procs.get(which)
            if proc is None:
                continue
            if proc.poll() is None:
                # 进程还活着 → 计数复位。原实现只在"看门狗自己拉起且健康检查成功"
                # 才清零 ✗ —— 外部把服务拉回来之后计数残留，退避态被永久化、
                # 每分钟误报"连续失败"（audit2 LOW ✓）。
                self.fails[which] = 0
                continue
            if self.stop_event.is_set():
                return
            code = proc.returncode
            self.fails[which] += 1
            self.restarts[which] += 1
            log(f"「看门狗」{which} 已退出（code={code}），第 {self.restarts[which]} 次拉起…")
            try:
                if self.stop_event.is_set():
                    return
                newp = self.spawn(which)
                ok = self.wait_ready(which, newp, 90 if which == "backend" else 30)
                if ok:
                    log(f"「看门狗」{which} 已恢复 ✓（累计重启 {self.restarts[which]} 次）")
                    self.fails[which] = 0
                else:
                    log(f"「看门狗」{which} 拉起后仍不可用 ✗"
                        f"（连续第 {self.fails[which]} 次）—— 详见 {_LOGDIR}\\"
                        f"{'backend' if which == 'backend' else 'adapter'}.log")
            except Exception as e:                         # noqa: BLE001
                log(f"「看门狗」拉起 {which} 失败: {type(e).__name__}: {e}")

    def run(self) -> None:
        while not self.stop_event.wait(WATCH_INTERVAL):
            self.check_once()
            # 连续挂 → 退避，别把日志刷爆（端口被占/依赖缺失时重启一百次也没用 ✓）
            if max(self.fails.values()) >= WATCH_BACKOFF_AFTER:
                log(f"「看门狗」连续失败 {self.fails}，退避 {WATCH_BACKOFF_INTERVAL:.0f} 秒")
                if self.stop_event.wait(WATCH_BACKOFF_INTERVAL):
                    return

    def shutdown(self) -> None:
        # 顺序很重要：**先置位**（让在途的 wait_ready 立刻让出 ✓）再回收进程 ✗
        self.stop_event.set()
        for which, p in list(self.procs.items()):
            try:
                p.terminate()
            except Exception:                                 # noqa: BLE001
                pass
            # 【只 terminate 不 wait 是不够的】子进程可能还没退、端口还占着，
            # 下一次启动会直接"端口被占" ✗（用户看到的就是"起不来"却查不出原因）。
            # 等一会儿，还没退就 kill 兜底；回收不掉要留痕，不许静默 ✓
            try:
                p.wait(timeout=8)
            except Exception:                                 # noqa: BLE001
                try:
                    p.kill()
                    p.wait(timeout=4)
                except Exception:                             # noqa: BLE001
                    log(f"「看门狗」{which} 未能回收（pid={p.pid}），可能残留")


def main() -> int:
    # 日志目录：后端的 stdout 落文件而不是控制台 —— 控制台只留本启动器自己的
    # 进度行（旧行为是别让日志盖在 TUI 上；TUI 已删，日志落盘保留）。
    logdir = _LOGDIR
    os.makedirs(logdir, exist_ok=True)
    backend_log = open(os.path.join(logdir, "backend.log"), "a",
                       encoding="utf-8", errors="replace")

    # 持久化根：`.lioncode`（会话元数据 / 对话历史）就落在这里。
    # 后端与适配层**必须用同一个值** —— 适配层要靠它找到对话文件来回放历史，
    # 否则只能靠候选搜索兜底。这里算一次、两边共用，避免以后改单边漂移。
    # 数据根必须用 `_LOGDIR`（它会回退到可写位置）✗ 不能写死 ROOT/.lbcheck
    workspace_root = os.path.join(_LOGDIR, "workspace")

    wd = Watchdog(workspace_root,
                  backend_log,
                  open(os.path.join(logdir, "adapter.log"), "a",
                       encoding="utf-8", errors="replace"))

    # ① 后端
    print(f"[1/3] 启动 Lion Code 后端 :{BACKEND_PORT} …", flush=True)
    backend = wd.spawn("backend")
    if not wd.wait_ready("backend", backend, 90):
        print("后端没起来，退出。", flush=True)
        backend.terminate()
        return 1
    print("      后端就绪", flush=True)

    # ② 适配层
    print(f"[2/3] 启动 MiMo 兼容接口层 :{ADAPTER_PORT} …", flush=True)
    adapter = wd.spawn("adapter")
    if not wd.wait_ready("adapter", adapter, 30):
        print("适配层没起来，退出。", flush=True)
        backend.terminate()
        adapter.terminate()
        return 1
    print("      适配层就绪", flush=True)

    # 看门狗开工（进入常驻等待之前就开，覆盖"刚起来那会儿崩掉"这种情况 ✓）
    wd.start()
    log(f"「看门狗」已启动：每 {WATCH_INTERVAL:.0f} 秒检查一次，只看后端与适配层")

    # ③ 界面已整体删除（tui/ 移除）—— 本脚本现在只管 后端 + 适配层 + 看门狗，
    # 挂在这里常驻等 Ctrl+C；界面走浏览器：http://127.0.0.1:<后端端口>/platform
    print(f"[3/3] 无终端界面（tui/ 已删除）—— 浏览器打开 http://127.0.0.1:{BACKEND_PORT}/platform",
          flush=True)
    print("按 Ctrl+C 停止后端与适配层。", flush=True)
    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        print("", flush=True)
        print("收到 Ctrl+C，收尾…", flush=True)
    # 【收尾顺序】先停看门狗 —— 否则收尾期间它会把刚 terminate 的服务又拉起来 ✓
    log("「看门狗」停止（用户退出）")
    wd.shutdown()
    # join 的超时要盖过 shutdown 里的等待（terminate→wait(8s)→kill→wait(4s) ≈ 12s）
    wd.join(timeout=20)
    if wd.is_alive():
        log("「看门狗」线程 20 秒后仍未退出（可能卡在健康检查），已放弃等待")
    log(f"收尾完成（本次累计重启：后端 {wd.restarts['backend']} 次 / "
        f"适配层 {wd.restarts['adapter']} 次）")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())