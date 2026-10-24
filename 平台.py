# -*- coding: utf-8 -*-
r"""TigerForge（虎铸）—— 项目 AI 开发平台。

【它是什么】在后端（main.py 的 HTTP 服务）上挂一个平台页 `/platform`：
用户填 项目名 / CPU 核数 / 内存 / 磁盘 / AI API / 开始提示词 → 平台用**现有 Agent 主循环**
（AgentLoop，与聊天、TUI 同一条链）在**专属工作区目录**里把项目构建出来；
构建完成后平台**自己把它跑起来做验证**（起进程 + HTTP 探活 + 取页面标题），通过才交付；
随后按产物形态自动部署：
  · 纯网页（web）        → 起服务并挂到 `/serve/<id>/`，用户直接访问
  · 纯客户端（client）   → 打 zip 挂到 `/dl/<id>/` 下载页
  · 前后端+客户端（三端）→ 网页照 web 部署，客户端照 client 出下载页
部署完用户仍可在平台页继续跟 AI 说话（同一条会话 ⇒ 同一份历史 ⇒ 改功能/修 bug）。

【资源从物理机分】创建项目时从物理机总量里划走 CPU 核数与内存：
  · 总量登记在 `<config>/platform/resources.json`（和为物理机上限，超额拒绝创建）
  · 运行时真正生效：CPU → SetProcessAffinityMask（亲和到前 N 核）
                   内存 → Windows Job Object 的 JobMemoryLimit（超限 OOM 杀进程）
  · 磁盘是配额登记：构建完核对实际占用，超了在日志与状态里如实标出
失败的限制不装死 —— 警告全部写进项目日志（honest over silent）。

【改动审核】Agent 写文件会进"待审改动"（ChangeReview）；平台构建是无人值守的，
所以构建/聊天期间由本模块的**放行线程**逐条 approve（产物由紧随其后的自测阶段验证）。
拿到闸门的方式：`工具.REVIEW_HOOK`（main 的 _wire_tool_hooks 挂上去的那一份）。

【诚实边界】
  · 自测 = "起得来 + HTTP 探活 + 页面标题"级别；应用层业务正确性由 Agent 自己写的
    自测脚本负责（提示词里明确要求它真跑真验）
  · 资源限制对**被启动的服务进程**生效；Agent 进程（后端自己）不在配额内
  · 下载页的 zip 是部署时打一次；项目更新后需要重新部署（POST /redeploy）
"""
from __future__ import annotations

import ctypes
import hashlib
import hmac
import ipaddress
import json
import os
import re
import secrets
import shutil
import socket
import subprocess
import sys
import tempfile
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import zipfile
from datetime import datetime
from pathlib import Path
from typing import Any, Callable

PLATFORM_NAME = "TigerForge"
PLATFORM_TAG = "虎铸 · 项目 AI 开发平台"
LOCK = threading.RLock()
#: 项目状态机：created → building → testing → deploying → live / failed / stopped
ST_CREATED, ST_BUILDING, ST_TESTING, ST_DEPLOYING, ST_LIVE, ST_FAILED, ST_STOPPED = (
    "created", "building", "testing", "deploying", "live", "failed", "stopped")
#: 支付成功后、虚拟机供给中（VBox 建克隆/装 Windows 阶段）
ST_PROVISIONING = "provisioning"
#: 网页服务探测上限（秒）—— 起得慢的应用给足时间，但不能无限等
PROBE_TIMEOUT = 40
CREATE_NO_WINDOW = 0x08000000


# ============================================================ 物理机资源
def physical_specs() -> dict[str, Any]:
    """物理机规格：核数 / 内存 MB / 磁盘可用 GB / 系统版本。"""
    cores = os.cpu_count() or 4
    ram_mb = 8192
    try:
        class _MSX(ctypes.Structure):
            _fields_ = [("dwLength", ctypes.c_uint32), ("dwMemoryLoad", ctypes.c_uint32),
                        ("ullTotalPhys", ctypes.c_uint64), ("ullAvailPhys", ctypes.c_uint64),
                        ("ullTotalPageFile", ctypes.c_uint64), ("ullAvailPageFile", ctypes.c_uint64),
                        ("ullTotalVirtual", ctypes.c_uint64), ("ullAvailVirtual", ctypes.c_uint64),
                        ("ullAvailExtendedVirtual", ctypes.c_uint64)]
        m = _MSX()
        m.dwLength = ctypes.sizeof(_MSX)
        if ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(m)):
            ram_mb = int(m.ullTotalPhys // (1024 * 1024))
    except Exception:                                       # noqa: BLE001 非 Windows/失败 → 兜底
        pass
    disk_gb = 0
    try:
        root = os.path.splitdrive(os.getcwd())[0] or "C:"
        free = shutil.disk_usage(root)
        disk_gb = int(free.total // (1024 ** 3))
    except Exception:                                       # noqa: BLE001
        pass
    os_name = ""
    try:
        os_name = " ".join(x for x in sys.getwindowsversion()[:3] if x) and \
            f"Windows {sys.getwindowsversion().major}.{sys.getwindowsversion().minor} (build {sys.getwindowsversion().build})"
    except Exception:                                       # noqa: BLE001
        os_name = sys.platform
    return {"cores": cores, "ramMb": ram_mb, "diskGb": disk_gb, "os": os_name}


def _free_port() -> int:
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        return int(s.getsockname()[1])


# ============================================================ 资源池
class ResourcePool:
    """项目运行时的资源登记与进程级强制。"""

    def __init__(self, state_path: Path) -> None:
        self.path = state_path
        self._alloc: dict[str, dict[str, Any]] = {}
        try:
            self._alloc = json.loads(state_path.read_text(encoding="utf-8"))
        except Exception:                                   # noqa: BLE001 没有/坏 → 空池
            pass

    def _save(self) -> None:
        try:
            self.path.parent.mkdir(parents=True, exist_ok=True)
            tmp = self.path.with_suffix(".tmp")
            tmp.write_text(json.dumps(self._alloc, ensure_ascii=False, indent=1), encoding="utf-8")
            os.replace(tmp, self.path)
        except OSError as e:
            print(f"[平台] 资源池落盘失败: {e}", flush=True)

    def used(self) -> dict[str, int]:
        cpu = sum(int(v.get("cpu", 0)) for v in self._alloc.values())
        mem = sum(int(v.get("memMb", 0)) for v in self._alloc.values())
        disk = sum(int(v.get("diskGb", 0)) for v in self._alloc.values())
        bw = sum(int(v.get("bwMb", 0)) for v in self._alloc.values())
        return {"cpu": cpu, "memMb": mem, "diskGb": disk, "bwMb": bw, "count": len(self._alloc)}

    def allocate(self, pid: str, cpu: int, mem_mb: int, disk_gb: int, bw_mb: int = 0) -> str | None:
        """登记配额；CPU/内存/磁盘超物理机总量返回原因（None = 成功）。
        【带宽只登记不设总上限】物理机没有可测的"总带宽"（取决于上联链路/网关），
        bw_mb 只做每实例记账 + 下发给部署服务（env LIMIT_BANDWIDTH_MBPS）；
        真限速要在网关/容器做 —— 详情页如实写明，不假装进程级能限。
        【重登记剔除自身】重复 allocate（重新部署/重新构建）时，已占用量要先减掉
        本实例的旧份额再校验 —— 否则满载机器上重部署会被"自己占的那份"误拒 ✗✗✗。"""
        specs = physical_specs()
        with LOCK:
            own = self._alloc.get(pid) or {}
            used = self.used()
            used_cpu = used["cpu"] - int(own.get("cpu", 0))
            used_mem = used["memMb"] - int(own.get("memMb", 0))
            used_disk = used["diskGb"] - int(own.get("diskGb", 0))
            if used_cpu + cpu > specs["cores"]:
                return f"CPU 配额不足：物理机 {specs['cores']} 核，已分配 {used_cpu}，本次要 {cpu}"
            if used_mem + mem_mb > specs["ramMb"]:
                return f"内存配额不足：物理机 {specs['ramMb']} MB，已分配 {used_mem}，本次要 {mem_mb}"
            if used_disk + disk_gb > max(specs["diskGb"], 10):
                return f"磁盘配额不足：本机 {specs['diskGb']} GB，已分配 {used_disk}，本次要 {disk_gb}"
            self._alloc[pid] = {"cpu": cpu, "memMb": mem_mb, "diskGb": disk_gb,
                                "bwMb": int(bw_mb or 0), "at": _now()}
            self._save()
        return None

    def release(self, pid: str) -> bool:
        """释放配额；返回这次是否真的释放了（幂等：没登记过返回 False）。"""
        with LOCK:
            if self._alloc.pop(pid, None) is not None:
                self._save()
                return True
        return False


def apply_process_limits(pid: int, cpu_cores: int, mem_mb: int) -> list[str]:
    """把 CPU/内存限制落到进程上；每条失败都变成警告（不吞）。"""
    warns: list[str] = []
    k32 = ctypes.windll.kernel32 if hasattr(ctypes, "windll") else None
    if k32 is None:
        return ["非 Windows：CPU/内存限制未生效"]
    # CPU 亲和：掩码前 N 位
    try:
        PROCESS_SET_INFORMATION = 0x0200
        h = k32.OpenProcess(PROCESS_SET_INFORMATION, False, pid)
        if not h:
            warns.append(f"OpenProcess(CPU) 失败 errno={ctypes.get_last_error()}")
        else:
            mask = (1 << max(1, min(cpu_cores, 64))) - 1
            ok = k32.SetProcessAffinityMask(h, ctypes.c_size_t(mask))
            k32.CloseHandle(h)
            if not ok:
                warns.append("SetProcessAffinityMask 失败")
    except Exception as e:                                   # noqa: BLE001
        warns.append(f"CPU 亲和设置异常: {e}")
    # 内存：Job Object 的 JobMemoryLimit（超限由系统 OOM 杀，而不是拖垮物理机）
    try:
        JOB_OBJECT_LIMIT_JOB_MEMORY = 0x200
        JobObjectExtendedLimitInformation = 9
        PROCESS_SET_QUOTA = 0x0100
        PROCESS_TERMINATE = 0x0001

        class _BASIC(ctypes.Structure):
            _fields_ = [("PerProcessUserTimeLimit", ctypes.c_int64),
                        ("PerJobUserTimeLimit", ctypes.c_int64),
                        ("LimitFlags", ctypes.c_uint32),
                        ("MinimumWorkingSetSize", ctypes.c_size_t),
                        ("MaximumWorkingSetSize", ctypes.c_size_t),
                        ("ActiveProcessLimit", ctypes.c_uint32),
                        ("Affinity", ctypes.c_size_t),
                        ("PriorityClass", ctypes.c_uint32),
                        ("SchedulingClass", ctypes.c_uint32)]

        class _IO(ctypes.Structure):
            _fields_ = [(n, ctypes.c_uint64) for n in
                        ("ReadOperationCount", "WriteOperationCount", "OtherOperationCount",
                         "ReadTransferCount", "WriteTransferCount", "OtherTransferCount")]

        class _EXT(ctypes.Structure):
            _fields_ = [("BasicLimitInformation", _BASIC), ("IoInfo", _IO),
                        ("ProcessMemoryLimit", ctypes.c_size_t), ("JobMemoryLimit", ctypes.c_size_t),
                        ("PeakProcessMemoryUsed", ctypes.c_size_t), ("PeakJobMemoryUsed", ctypes.c_size_t)]

        job = k32.CreateJobObjectW(None, None)
        if not job:
            warns.append("CreateJobObject 失败")
            return warns
        info = _EXT()
        info.BasicLimitInformation.LimitFlags = JOB_OBJECT_LIMIT_JOB_MEMORY
        info.JobMemoryLimit = int(mem_mb) * 1024 * 1024
        if not k32.SetInformationJobObject(job, JobObjectExtendedLimitInformation,
                                           ctypes.byref(info), ctypes.sizeof(info)):
            warns.append("SetInformationJobObject 失败")
            return warns
        ph = k32.OpenProcess(PROCESS_SET_QUOTA | PROCESS_TERMINATE, False, pid)
        if not ph:
            warns.append(f"OpenProcess(内存配额) 失败 errno={ctypes.get_last_error()}")
            return warns
        ok = k32.AssignProcessToJobObject(job, ph)
        k32.CloseHandle(ph)
        if not ok:
            warns.append("AssignProcessToJobObject 失败")
    except Exception as e:                                   # noqa: BLE001
        warns.append(f"内存限制设置异常: {e}")
    return warns


# ============================================================ 存储
def _now() -> str:
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def _atomic_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(payload, ensure_ascii=False, indent=1), encoding="utf-8")
    os.replace(tmp, path)


class ProjectStore:
    def __init__(self, path: Path) -> None:
        self.path = path
        self._items: list[dict[str, Any]] = []
        try:
            self._items = json.loads(path.read_text(encoding="utf-8"))
        except Exception:                                   # noqa: BLE001
            pass

    def save(self) -> None:
        with LOCK:
            _atomic_json(self.path, self._items)

    def all(self) -> list[dict[str, Any]]:
        with LOCK:
            return [dict(p) for p in self._items]

    def get(self, pid: str) -> dict[str, Any] | None:
        with LOCK:
            for p in self._items:
                if p["id"] == pid:
                    return dict(p)
        return None

    def update(self, pid: str, **fields: Any) -> None:
        with LOCK:
            for p in self._items:
                if p["id"] == pid:
                    p.update(fields)
                    break
        self.save()

    def add(self, item: dict[str, Any]) -> None:
        with LOCK:
            self._items.append(item)
        self.save()

    def remove(self, pid: str) -> bool:
        """整条删除实例记录（IP 随记录消失 = 归还池 —— 池的 taken 读的就是记录）。"""
        with LOCK:
            before = len(self._items)
            self._items = [p for p in self._items if p.get("id") != pid]
            changed = len(self._items) != before
            if changed:
                _atomic_json(self.path, self._items)
        return changed


# ============================================================ 账号 / 计费 / IP 池
# ============ 价格表（钱一律用整数分，绝不浮点；与售卖口径逐字一致）============
#: 实例基础月租（CPU+内存，分/月）：1C1G=11 2C2G=20 4C8G=38 8C16G=69 元
BASE_MONTH_CENTS = {"1C1G": 1100, "2C2G": 2000, "4C8G": 3800, "8C16G": 6900}
#: 实例包年（分/年，**8 折仅算力内存**；IP/硬盘不打折）：
#: 106 / 192 / 365 / 662 元
BASE_YEAR_CENTS = {"1C1G": 10600, "2C2G": 19200, "4C8G": 36500, "8C16G": 66200}
#: 分项：独立公网 IP 6 元/个/月；HDD 0.06 元/G/月；出站流量 0.5 元/GB
IP_MONTH_CENTS = 600
DISK_GB_MONTH_CENTS = 6
TRAFFIC_GB_CENTS = 50
#: 计费周期（秒）
CYCLE_SECONDS = {"month": 30 * 86400, "year": 365 * 86400}


def price_cents(spec: str, cpu: int, mem_mb: int, cycle: str = "month") -> int:
    """一期**算力**价（分）：月=月租表；年=包年表（8 折仅算力）。
    自定义档线性兜底 500·核 + 600·GB/月（1C1G 正好 1100 ✓），年 = ×12×0.8。"""
    table = BASE_YEAR_CENTS if cycle == "year" else BASE_MONTH_CENTS
    if spec in table:
        return table[spec]
    m = 500 * max(1, int(cpu)) + 600 * max(1, int(mem_mb) // 1024)
    return int(m * 12 * 0.8) if cycle == "year" else m


def extras_month_cents(disk_gb: int, has_ip: bool) -> int:
    """分项每月（分）：HDD + 独立 IP —— 不参与包年 8 折。"""
    return int(disk_gb) * DISK_GB_MONTH_CENTS + (IP_MONTH_CENTS if has_ip else 0)


def traffic_cents(egress_bytes: int) -> int:
    """未结出站流量折分（0.5 元/GB，按字节折算不四舍五入到整 GB）。"""
    return int(round(int(egress_bytes) / (1024 ** 3) * TRAFFIC_GB_CENTS))


def period_total_cents(spec: str, cpu: int, mem_mb: int, disk_gb: int, has_ip: bool,
                       cycle: str, egress_bytes: int = 0) -> int:
    """一期应付（分）= 算力（月租或包年）+ 分项×（年则 ×12）+ 未结出站流量。"""
    months = 12 if cycle == "year" else 1
    return (price_cents(spec, cpu, mem_mb, cycle)
            + extras_month_cents(disk_gb, has_ip) * months
            + traffic_cents(egress_bytes))


def _hash_pw(password: str, salt: str) -> str:
    """口令哈希（sha256+salt）。**换挡位的口子**就在这个函数与 AuthStore.verify：
    生产要抗爆破请换成 argon2/bcrypt —— 本项目 Python 侧第三方依赖为 0，先用标准库
    实现并把换法写在这里（诚实边界，不假装这是 bcrypt）。"""
    return hashlib.sha256((salt + ":" + password).encode("utf-8")).hexdigest()


#: 单条消息入库上限（字符；超出截断并如实标注在内容尾部）
_MSG_CAP = 65536


def _sql_str(s: str) -> str:
    r"""手工 SQL **字符串字面量**（只用于对话内容这类自由文本；用户名等受约束值不走这）。

    顺序要紧：先 `\` → `\\` 再 `'` → `\'`（反了会把转义本身转坏）；`\x00` 剔除
    （MySQL 文本列非法字节）。内容只当**数据**放字面量、两种危险字符都被转义 ⇒
    默认 sql_mode 下无注入位。README 注明：若服务器显式开了 NO_BACKSLASH_ESCAPES
    需要回头改这里（不装看不见）。"""
    t = str(s).replace("\x00", "")
    if len(t) > _MSG_CAP:
        t = t[:_MSG_CAP] + " …[超长截断]"
    return "'" + t.replace("\\", "\\\\").replace("'", "\\'") + "'"


class _Breaker:
    """云端模型**限流熔断器**（用户: "你不限流" —— 收到，补上）。

    云端 429/401/网络失败 → 开闸冷却：10 分钟起、翻倍、30 分钟封顶；期间平台自己
    限流（购买/重建/对话全部友好拒绝并报"还剩几分钟"），**不再往云端撞**（每撞一次
    都要浪费3次重试的时间还吓用户）。任何一次成功调用即闭合（零等待恢复）。"""

    def __init__(self, path: str | os.PathLike[str] | None = None) -> None:
        self.open_until = 0.0
        self.strikes = 0
        self.lock = threading.Lock()
        # 【状态落盘】内存态熔断会被后端重启清零 ⇒ 每次重启"门又开一次"、用户又买
        # 一单又死（连环报障实证 ✗✗✗✗✗）—— 持久化到平台目录/breaker.json，重启
        # 恢复；只有真成功（ok）才归零。
        self._path = (Path(str(path)) / "breaker.json") if path else None
        self._load()

    def _load(self) -> None:
        if self._path is None:
            return
        try:
            d = json.loads(self._path.read_text(encoding="utf-8"))
            self.open_until = float(d.get("open_until") or 0.0)
            self.strikes = int(d.get("strikes") or 0)
        except (OSError, ValueError):
            pass

    def _save(self) -> None:
        if self._path is None:
            return
        try:
            self._path.parent.mkdir(parents=True, exist_ok=True)
            self._path.write_text(json.dumps({"open_until": self.open_until,
                                              "strikes": self.strikes}), encoding="utf-8")
        except OSError:
            pass

    def fail(self) -> float:
        """记录一次模型失败；返回新的开闸截止时间（并落盘）。"""
        with self.lock:
            now = time.time()
            self.strikes += 1
            cool = min(600 * (2 ** (self.strikes - 1)), 1800)
            self.open_until = max(self.open_until, now + cool)
            self._save()
            return self.open_until

    def ok(self) -> None:
        """成功即闭合、清零计数（并落盘）。"""
        with self.lock:
            self.strikes = 0
            self.open_until = 0.0
            self._save()

    def left(self) -> int:
        return max(0, int(self.open_until - time.time()))

    def tripped(self) -> bool:
        return self.left() > 0

    def msg(self) -> str:
        left = self.left()
        return (f"云端限流冷却中（第{self.strikes}波失败）—— 还剩 {left // 60} 分 {left % 60} 秒；"
                f"任一调用成功会自动恢复（探测: .lbcheck/probe_model_key.py）")


def _mysql_cfg() -> dict[str, Any] | None:
    """解析 `LION_MYSQL_DSN`（mysql://user:pass@host:3306/db）；没配 → None（JSON 模式）。

    【为什么用 CLI 而不是驱动】Python 侧第三方依赖为 0（不装 pymysql/mysql-connector），
    所以账号库走 `mysql` 客户端进程：登录名受正则约束、token/salt/hash 全是 hex/数字，
    拼进 SQL 不存在注入面；密码走 --defaults-extra-file（不出现在进程列表）。
    """
    dsn = os.environ.get("LION_MYSQL_DSN") or ""
    if not dsn:
        return None
    u = urllib.parse.urlparse(dsn)
    if u.scheme not in ("mysql", "mysql2") or not (u.hostname and u.username
                                                   and (u.path or "").lstrip("/")):
        return {"error": "DSN 必须形如 mysql://user:pass@host:3306/dbname"}
    pw = urllib.parse.unquote(u.password or "")
    if '"' in pw:
        return {"error": "DSN 密码暂不支持双引号字符（cnf 转义会失真）"}
    return {"host": u.hostname, "port": str(u.port or 3306),
            "user": urllib.parse.unquote(u.username or ""), "password": pw,
            "database": (u.path or "/").lstrip("/")}


def _mysql_client_bin() -> str:
    """找 mysql 客户端：env 指定 → PATH → 常见安装位。`.py`/`.cmd` 后缀由执行层处理
    （测试用伪客户端脚本走 .py 这条 ✓）。"""
    for cand in (os.environ.get("LION_MYSQL_CLIENT") or "",
                 shutil.which("mysql") or "",
                 r"C:\Program Files\MySQL\MySQL Server 8.0\bin\mysql.exe",
                 r"C:\Program Files\MySQL\MySQL Server 8.4\bin\mysql.exe",
                 r"C:\Program Files (x86)\MySQL\MySQL Server 8.0\bin\mysql.exe"):
        if cand and os.path.isfile(cand):
            return cand
    return ""


class AuthStore:
    """账号、余额（分）、登录会话。

    **users.json 为空 = 未启用鉴权（开放模式）** —— 没人部署账号体系时，
    全部行为与加这个模块之前逐字一致；管理员建了第一个账号，鉴权从此生效。
    """
    TTL = 7 * 86400            # 会话 7 天

    def __init__(self, directory: Path) -> None:
        self._users_path = directory / "users.json"
        self._sess_path = directory / "auth_sessions.json"
        self.users: dict[str, dict[str, Any]] = {}
        self.sessions: dict[str, dict[str, Any]] = {}
        #: 登录失败记账 {f"{user}|{ip}": {"n": 次数, "until": 解封时间}} —— 内存态
        #: （重启即清，见 README 安全注记；5 次失败锁 60s 起，随次数涨）
        self._fails: dict[str, dict[str, float]] = {}
        try:
            self.users = json.loads(self._users_path.read_text(encoding="utf-8"))
        except Exception:                                   # noqa: BLE001 没有/坏 → 开放模式
            pass
        try:
            self.sessions = json.loads(self._sess_path.read_text(encoding="utf-8"))
        except Exception:                                   # noqa: BLE001
            pass
        # ===== MySQL 账号库（LION_MYSQL_DSN 配了才启用；失败降级 JSON 并出声）=====
        self._my_cfg = _mysql_cfg()
        self._my_bin = _mysql_client_bin()
        self._my_warn: set[str] = set()
        self.account_db = "json"
        if self._my_cfg is not None:
            if self._my_cfg.get("error"):
                self._my_fail("dsn", str(self._my_cfg["error"]))
            elif not self._my_bin:
                self._my_fail("client", "配了 LION_MYSQL_DSN 但找不到 mysql 客户端"
                                        "（设 LION_MYSQL_CLIENT 指向 mysql.exe）")
            elif self._my_boot_mysql():
                self.account_db = (f"mysql:{self._my_cfg['host']}/{self._my_cfg['database']}")

    # ---- MySQL 后端（账号/会话；写穿 + 降级） ----
    def _my_fail(self, what: str, msg: str) -> None:
        if what not in self._my_warn:
            self._my_warn.add(what)
            print(f"[平台] ⚠ 账号库 MySQL({what}) 不可用，已降级 JSON: {msg}", flush=True)

    def _my_run(self, sql: str) -> list[list[str]] | None:
        r"""跑一条 SQL，返回 TSV 行（--skip-column-names）；任何失败 → None 并出声。

        注入面：用户名注册时正则 `[\w.\-]{2,32}` 约束、token/salt/hash 均 hex/数字、
        余额是 int —— 拼进去的动态值都不含引号，没有注入位（README 注明这条前提）。
        """
        if not (self._my_cfg and self._my_bin):
            return None
        cfg = self._my_cfg
        cnf = self._users_path.parent / "mysql.cnf"
        try:
            cnf.parent.mkdir(parents=True, exist_ok=True)
            cnf.write_text("[client]\nhost=%s\nport=%s\nuser=%s\npassword=%s\ndatabase=%s\n"
                           % (cfg["host"], cfg["port"], cfg["user"],
                              cfg["password"], cfg["database"]),
                           encoding="utf-8")
        except OSError as e:
            self._my_fail("cnf", str(e))
            return None
        first = [f"--defaults-extra-file={cnf}", "--batch", "--skip-column-names", "-e", sql]
        binp = self._my_bin
        if binp.lower().endswith(".py"):
            cmd = [sys.executable, binp, *first]
        elif binp.lower().endswith((".cmd", ".bat")):
            cmd = ["cmd", "/c", binp, *first]
        else:
            cmd = [binp, *first]
        try:
            r = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8",
                               errors="replace", timeout=15)
        except Exception as e:                               # noqa: BLE001
            self._my_fail("run", f"{type(e).__name__}: {e}")
            return None
        if r.returncode != 0:
            self._my_fail("sql", ((r.stderr or "").strip() or f"rc={r.returncode}")[-300:])
            return None
        return [line.split("\t") for line in (r.stdout or "").splitlines() if line]

    def _my_boot_mysql(self) -> bool:
        """建表 → DB 主导加载（会话跨重启存活 = 比 JSON 更强）；DB 空而 JSON 有 → 迁移。"""
        if self._my_run("CREATE TABLE IF NOT EXISTS lion_users ("
                        "username VARCHAR(32) PRIMARY KEY, salt CHAR(16) NOT NULL, "
                        "hash CHAR(64) NOT NULL, balance BIGINT NOT NULL DEFAULT 0, "
                        "admin TINYINT NOT NULL DEFAULT 0, created_at VARCHAR(19) NOT NULL)"
                        ) is None:
            return False
        if self._my_run("CREATE TABLE IF NOT EXISTS lion_sessions ("
                        "token CHAR(40) PRIMARY KEY, username VARCHAR(32) NOT NULL, "
                        "exp BIGINT NOT NULL, KEY idx_user (username))") is None:
            return False
        # 对话永久存储（用户↔AI 每轮双写: 项目内 chat.jsonl + 本表；表在启动自动建）
        if self._my_run("CREATE TABLE IF NOT EXISTS lion_messages ("
                        "id BIGINT AUTO_INCREMENT PRIMARY KEY, "
                        "session_id CHAR(40) NOT NULL, project_id VARCHAR(48) NOT NULL, "
                        "owner VARCHAR(32) NOT NULL DEFAULT '', role VARCHAR(8) NOT NULL, "
                        "content MEDIUMTEXT NOT NULL, created_at VARCHAR(19) NOT NULL, "
                        "KEY idx_proj (project_id), KEY idx_sess (session_id))") is None:
            return False
        rows = self._my_run("SELECT username,salt,hash,balance,admin,created_at FROM lion_users")
        if rows is None:
            return False
        db_users = {}
        for r in rows:
            if len(r) >= 6:
                db_users[r[0]] = {"salt": r[1], "hash": r[2], "balance": int(r[3] or 0),
                                  "admin": bool(int(r[4] or 0)), "createdAt": r[5]}
        if db_users:
            self.users = db_users                            # DB 权威
        elif self.users:
            for name, u in list(self.users.items()):         # JSON → MySQL 一次性迁移
                self._my_run(
                    "INSERT IGNORE INTO lion_users VALUES ('%s','%s','%s',%d,%d,'%s')"
                    % (name, u.get("salt", ""), u.get("hash", ""),
                       int(u.get("balance", 0) or 0),
                       1 if u.get("admin") else 0,
                       str(u.get("createdAt") or _now())))
        srows = self._my_run("SELECT token,username,exp FROM lion_sessions")
        if srows is not None:
            now = time.time()
            self.sessions = {r[0]: {"user": r[1], "exp": float(r[2])}
                             for r in srows if len(r) >= 3 and float(r[2] or 0) > now}
        self._my_run("DELETE FROM lion_sessions WHERE exp < %d" % int(time.time()))
        return True

    @property
    def enabled(self) -> bool:
        return bool(self.users)

    #: login() 的"已锁定"哨兵（含非 hex 字符，与真 token 不冲突）
    LOCKED = "__locked__"

    def _save_users(self) -> None:
        _atomic_json(self._users_path, self.users)

    def _save_sessions(self) -> None:
        # 存前修剪：过期即弃 + 总量封顶（否则疯狂登录/长期运行会让文件无限长 ✗✗✗）
        now = time.time()
        alive = {k: v for k, v in self.sessions.items() if float(v.get("exp", 0)) > now}
        if len(alive) > 500:
            alive = dict(sorted(alive.items(),
                                key=lambda kv: float(kv[1].get("exp", 0)))[-500:])
        self.sessions = alive
        _atomic_json(self._sess_path, self.sessions)
        # MySQL 模式同步清过期行（exp 是自增epoch整数，安全拼接）
        if self._my_cfg and self._my_bin:
            self._my_run("DELETE FROM lion_sessions WHERE exp < %d" % int(now))

    def create_user(self, username: str, password: str, admin: bool = False) -> str | None:
        username = username.strip()
        if not re.fullmatch(r"[\w.\-]{2,32}", username):
            return "用户名需为 2-32 位字母/数字/._-"
        if len(password) < 6:
            return "密码至少 6 位"
        # 【必须上锁】两个并发"首个注册"都能看到 users 为空 ⇒ 双管理员 ✗✗✗
        with LOCK:
            if username in self.users:
                return "用户名已存在"
            salt = secrets.token_hex(8)
            adm = bool(admin) or not self.users
            created = _now()
            self.users[username] = {
                "salt": salt,
                "hash": _hash_pw(password, salt),
                "balance": 0,
                # 第一个账号天然当管理员（部署者本人）
                "admin": adm,
                "createdAt": created,
            }
            self._save_users()
            self._my_run("INSERT IGNORE INTO lion_users VALUES ('%s','%s','%s',0,%d,'%s')"
                         % (username, salt, self.users[username]["hash"],
                            1 if adm else 0, created))
        return None

    def verify(self, username: str, password: str) -> bool:
        u = self.users.get(username.strip())
        if not u:
            # 用户不存在也做一次同代价哈希（否则"用户不存在"与"密码错"响应时间不同
            # = 账号枚举的侧信道）
            _hash_pw(password, "dummy-salt-for-timing")
            return False
        return hmac.compare_digest(_hash_pw(password, u["salt"]), u["hash"])

    def is_admin(self, username: str | None) -> bool:
        return bool(username and self.users.get(username, {}).get("admin"))

    def balance(self, username: str | None) -> int:
        if not username:
            return 0
        return int(self.users.get(username, {}).get("balance", 0))

    def credit(self, username: str, cents: int) -> None:
        with LOCK:
            u = self.users.get(username)
            if u is not None:
                u["balance"] = int(u.get("balance", 0)) + int(cents)
                self._save_users()
                self._my_run("UPDATE lion_users SET balance=%d WHERE username='%s'"
                             % (u["balance"], username))

    def charge(self, username: str, cents: int) -> bool:
        """扣费（分）。**必须上锁** —— 并发两个购买都过"余额够"检查就成双花
        （ThreadingHTTPServer 真并发，实测推演 ✗✗✗）。余额不够整体拒绝、不产生欠款。"""
        with LOCK:
            u = self.users.get(username)
            if u is None:
                return False
            cur = int(u.get("balance", 0))
            if cur < cents:
                return False
            u["balance"] = cur - cents
            self._save_users()
            self._my_run("UPDATE lion_users SET balance=%d WHERE username='%s'"
                         % (u["balance"], username))
        return True

    def login(self, username: str, password: str, client: str = "") -> str | None:
        """返回 token / None（凭据错）/ LOCKED（爆破锁定）。

        限速：同 用户|IP 5 次失败锁 60s，之后每多失败一次翻倍（上限 30 分钟）。
        没有任何限速的话，无界密码爆破是本服务最便宜的攻击面 ✗✗✗。
        """
        key = f"{username.strip().lower()}|{client}"
        now = time.time()
        # 顺手修剪过期的失败记账（防字典无限涨）
        if len(self._fails) > 2000:
            self._fails = {k: v for k, v in self._fails.items() if v.get("until", 0) > now}
        rec = self._fails.get(key)
        if rec and rec.get("until", 0) > now:
            return self.LOCKED
        if not self.verify(username, password):
            with LOCK:
                rec = self._fails.setdefault(key, {"n": 0.0, "until": 0.0})
                rec["n"] = rec.get("n", 0) + 1
                if rec["n"] >= 5:
                    # 60s 起翻倍、15 分钟封顶（30 分钟对真人太狠 ✗✗✗）
                    rec["until"] = now + min(60 * 2 ** (rec["n"] - 5), 900)
            return None
        with LOCK:
            self._fails.pop(key, None)
            token = secrets.token_hex(20)
            self.sessions[token] = {"user": username.strip(), "exp": now + self.TTL}
            self._save_sessions()
            self._my_run("INSERT IGNORE INTO lion_sessions VALUES ('%s','%s',%d)"
                         % (token, username.strip(), int(now + self.TTL)))
        return token

    def logout(self, token: str) -> None:
        with LOCK:
            if self.sessions.pop(token, None) is not None:
                self._save_sessions()
                # token 来自 cookie（外部输入）—— 必须先验 40hex 才能拼 SQL ✗✗✗
                if re.fullmatch(r"[0-9a-f]{40}", token or ""):
                    self._my_run("DELETE FROM lion_sessions WHERE token='%s'" % token)

    def user_of(self, token: str | None) -> str | None:
        if not token:
            return None
        s = self.sessions.get(token)
        if not s:
            return None
        if float(s.get("exp", 0)) < time.time():
            with LOCK:
                self.sessions.pop(token, None)
                self._save_sessions()
            return None
        return s.get("user") or None

    def lock_left(self, username: str, client: str) -> int:
        """当前登录锁定剩余秒数（0=未锁）—— 锁提示必须带倒计时，
        否则用户只看到'稍后再试'无从等待（报障实测 ✗✗✗）。"""
        rec = self._fails.get(f"{str(username).strip().lower()}|{client}")
        if not rec:
            return 0
        return max(0, int(float(rec.get("until", 0)) - time.time()))


class BillingStore:
    """账单流水（分，最近 2000 条滚动保留）。kind: create / hourly / topup /
    stop-nobalance / system。充值没有真实支付网关 —— 见 README「充值占位」。"""

    def __init__(self, directory: Path) -> None:
        self.path = directory / "billing.json"
        self.rows: list[dict[str, Any]] = []
        try:
            self.rows = json.loads(self.path.read_text(encoding="utf-8"))
        except Exception:                                   # noqa: BLE001
            pass

    def add(self, kind: str, user: str, pid: str, spec: str, cents: int,
            note: str = "") -> None:
        with LOCK:
            self.rows.append({"at": _now(), "kind": kind, "user": user,
                              "projectId": pid, "spec": spec,
                              "cents": int(cents), "note": note})
            if len(self.rows) > 2000:
                self.rows = self.rows[-2000:]
            try:
                _atomic_json(self.path, self.rows)
            except OSError as e:
                print(f"[平台] 账单落盘失败（内存里还在）: {e}", flush=True)

    def list(self, user: str | None = None, limit: int = 50) -> list[dict[str, Any]]:
        rows = [r for r in self.rows if user is None or r.get("user") == user]
        return list(reversed(rows[-limit:]))


class IpPool:
    """独立 IP 池（ips.json）。

    每台用户的服务器要自带独立 IP —— 单机多实例的落法：
      ① 运维把真实 IP 先绑到网卡（netsh，需管理员）再加进池；
      ② 购买（创建项目）时从池里分一个，**分不到就如实拒绝购买**（池空=未配置，
         购买照常但顶栏明示"IP 池未配置"，不假装有独立 IP）；
      ③ 路由按 **Host（目标 IP）** 直达该实例（见 PlatformApi.http_gate）——
         不需要每实例单独监听。
    127.x 环回段本机就能 bind，用来做验证与演示（E2E 用 127.0.0.55 实测过 ✓）。
    """

    def __init__(self, directory: Path) -> None:
        self.path = directory / "ips.json"
        self.pool: list[str] = []
        try:
            self.pool = list(json.loads(self.path.read_text(encoding="utf-8")).get("pool", []))
        except Exception:                                   # noqa: BLE001
            pass

    def add(self, ip: str) -> str | None:
        ip = ip.strip()
        try:
            ipaddress.ip_address(ip)
        except ValueError:
            return f"非法 IP: {ip}"
        if ip in self.pool:
            return "IP 已在池中"
        self.pool.append(ip)
        _atomic_json(self.path, {"pool": self.pool})
        return None

    def remove(self, ip: str) -> bool:
        if ip in self.pool:
            self.pool.remove(ip)
            _atomic_json(self.path, {"pool": self.pool})
            return True
        return False

    def free(self, taken: set[str]) -> str | None:
        for ip in self.pool:
            if ip not in taken:
                return ip
        return None


def ip_on_this_machine(ip: str) -> bool:
    """IP 是不是本机网卡上的地址：bind 一次即知（非本机地址 Windows 直接
    WSAEADDRNOTAVAIL 拒绝）。环回段 127.x 一律 True（本机可直达）。"""
    try:
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.bind((ip, 0))
        return True
    except OSError:
        return False


def _vbox_status() -> dict[str, Any]:
    m = VBoxManager()
    ok, why = m.available()
    return {"available": ok, "reason": why, "mgmt": m.mgmt}


class VBoxManager:
    """VirtualBox 实例供给（VBoxManage CLI，零第三方依赖）。

    两条供给路（环境变量选）：
      ① **金镜像链接克隆（推荐）** `LION_VBOX_BASE=<预装 Windows 的基座 VM 名>`：
         Windows 只在做基座时装一次；购买 = clonevm(链接克隆) → 改 CPU/内存 →
         挂 10-100G 数据盘 → NAT 端口转发 → 启动。
      ② **新建+无人值守安装** `LION_WINDOWS_ISO=<Win ISO 路径>`：createvm → 建系统盘
         + 数据盘 → `unattended install`（自动装完 Windows）→ 启动。
    两条都没配 → available()=False 并给出改法（不静默）。
    本沙箱：VirtualBox 已装但 **固件虚拟化=False ⇒ startvm 起不来** —— 上层会
    收到失败并**全额退款**（支付后没拿到机器必须退）；伪 VBoxManage 可全链测状态机。
    """

    def __init__(self) -> None:
        self.mgmt = (os.environ.get("LION_VBOXMANAGE") or shutil.which("VBoxManage")
                     or next((p for p in (r"C:\Program Files\Oracle\VirtualBox\VBoxManage.exe",
                                          r"C:\Program Files\VirtualBox\VBoxManage.exe")
                              if os.path.isfile(p)), ""))

    def available(self) -> tuple[bool, str]:
        if not self.mgmt:
            return False, "未找到 VBoxManage（装 VirtualBox 或设 LION_VBOXMANAGE 路径）"
        if os.environ.get("LION_VBOX_BASE") or os.environ.get("LION_WINDOWS_ISO"):
            return True, "VirtualBox 可用（%s）" % ("金镜像" if os.environ.get("LION_VBOX_BASE")
                                                 else "无人值守安装")
        return False, ("VirtualBox 在但未配置供给方式：设 LION_VBOX_BASE（金镜像，推荐）"
                       "或 LION_WINDOWS_ISO（自动装 Windows 的 ISO）")

    def run(self, args: list[str], timeout: int = 600, log=None) -> tuple[int, str]:
        if self.mgmt.lower().endswith(".py"):          # 伪客户端（测试）走解释器
            cmd = [sys.executable, self.mgmt, *args]
        else:
            cmd = [self.mgmt, *args]
        if log:
            log("$ VBoxManage " + " ".join(args[:9]) + (" …" if len(args) > 9 else ""))
        try:
            r = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8",
                               errors="replace", timeout=timeout)
        except subprocess.TimeoutExpired:
            return 124, f"超时({timeout}s): {' '.join(cmd[:6])}"
        except OSError as e:
            return 127, f"{type(e).__name__}: {e}"
        out = ((r.stdout or "") + (r.stderr or "")).strip()
        if log and out:
            for ln in out.splitlines()[:12]:
                log("  | " + ln[:160])
        return r.returncode, out

    @staticmethod
    def _diskdir() -> str:
        d = os.environ.get("LION_VBOX_DISKDIR") or os.path.join(
            os.environ.get("LOCALAPPDATA", tempfile.gettempdir()), "TigerForge", "vm")
        os.makedirs(d, exist_ok=True)
        return d

    def provision(self, name: str, cpu: int, mem_mb: int, disk_gb: int, log) -> dict[str, Any]:
        """建一台装好 Windows 的 VM 并启动；任何一步非 0 → RuntimeError（上层退款）。"""
        base = os.environ.get("LION_VBOX_BASE")
        iso = os.environ.get("LION_WINDOWS_ISO")
        if base:
            rc, out = self.run(["clonevm", base, "--mode=machine", "--name", name,
                                "--register"], log=log)
            if rc:
                raise RuntimeError(f"克隆基座 {base} 失败: {out[-400:]}")
            steps = [["modifyvm", name, "--memory", str(mem_mb), "--cpus", str(cpu),
                      "--nic1", "nat"],
                     ["modifyvm", name, "--natpf1",
                      "web,tcp,,," + os.environ.get("LION_VBOX_WEB_PORT", "8081") + ",,80"]]
        else:
            if not iso:
                raise RuntimeError("既没配 LION_VBOX_BASE 也没配 LION_WINDOWS_ISO，"
                                   "无法创建带 Windows 的虚拟机")
            rc, out = self.run(["createvm", "--name", name, "--ostype", "Windows11_64",
                                "--register"], log=log)
            if rc:
                rc, out = self.run(["createvm", "--name", name, "--ostype", "Win10_64",
                                    "--register"], log=log)
            if rc:
                raise RuntimeError(f"createvm 失败: {out[-400:]}")
            diskdir = self._diskdir()
            sys_vdi = os.path.join(diskdir, f"{name}.vdi")
            data_vdi = os.path.join(diskdir, f"{name}-data.vdi")
            steps = [["modifyvm", name, "--memory", str(mem_mb), "--cpus", str(cpu),
                      "--nic1", "nat"],
                     ["createmedium", "disk", "--filename", sys_vdi,
                      "--size", str(max(10240, disk_gb * 1024)), "--format", "VDI"],
                     ["storagectl", name, "--name", "SATA", "--add", "sata",
                      "--portcount", "4"],
                     ["storageattach", name, "--storagectl", "SATA", "--port", "0",
                      "--device", "0", "--type", "hdd", "--medium", sys_vdi],
                     ["createmedium", "disk", "--filename", data_vdi,
                      "--size", str(disk_gb * 1024), "--format", "VDI"],
                     ["storageattach", name, "--storagectl", "SATA", "--port", "1",
                      "--device", "0", "--type", "hdd", "--medium", data_vdi]]
        for args in steps:
            rc, out = self.run(args, log=log)
            if rc:
                raise RuntimeError(f"{' '.join(args[:3])} 失败: {out[-400:]}")
        if not base:
            rc, out = self.run(["unattended", "install", name, f"--iso={iso}",
                                "--user=lion", "--password=TigerForge!2026",
                                "--locale=zh-CN", "--time-zone=Asia/Shanghai"],
                               timeout=5400, log=log)
            if rc:
                raise RuntimeError(f"无人值守安装 Windows 失败: {out[-400:]}")
        rc, out = self.run(["startvm", name, "--type", "headless"], timeout=600, log=log)
        if rc and "already" not in out.lower() and "已在运行" not in out:
            raise RuntimeError(f"启动 VM 失败（本机可能未开硬件虚拟化）: {out[-400:]}")
        ip = None
        rc, out = self.run(["guestproperty", "wait", name,
                            "/virtualbox/GuestInfo/Net/0/V4/IP", "--timeout", "180000"],
                           timeout=200, log=log)
        if rc == 0:
            for ln in out.splitlines():
                if ln.strip().startswith("Value:"):
                    ip = ln.split(":", 1)[1].strip()
        return {"vm": name, "ip": ip,
                "mode": ("golden-clone" if base else "fresh-unattended")}


# ============================================================ 主体
class PlatformApi:
    """/platform 页面 + /api/platform/* 接口 + /serve /dl 部署出口。"""

    def __init__(self, ctx: Any, Response: Any) -> None:
        self.ctx = ctx
        self.Response = Response
        base = Path(getattr(getattr(ctx, "cfg", None), "base", None) or (Path.home() / ".lioncode"))
        # 【数据目录必须"首选 → 可写回退"两段式】裸跑 `python main.py` 时配置目录是
        # `~/.lioncode`，本沙箱写不了（WinError 5）✗✗✗ 实测：建目录一抛，整个
        # platform 模块装配失败 ⇒ /platform 404"没有这个接口"（repro18081 完整复现）。
        # 本仓库其它装配失败都是"未完成（其余功能继续）"的降级 —— 平台也必须降级：
        #   ① LION_PLATFORM_DIR（运维显式指定，优先）
        #   ② 配置目录 platform/（正常机器走这条，行为零变化）
        #   ③ 系统临时目录兜底（沙箱里必可写；醒目告警 + 页面顶栏显示"降级"）
        env_dir = os.environ.get("LION_PLATFORM_DIR")
        preferred = Path(env_dir) if env_dir else (base / "platform")
        self.degraded = ""
        self.dir: Path | None = None
        last_err: OSError | None = None
        # 回退顺序有讲究：先试 cwd/.lbcheck —— 仓库和安装目录都有 .lbcheck 惯例
        # （已 gitignore/已属运行时产物）✓；最后才轮到系统临时目录。
        # 【为什么不能直接用 tempfile】本沙箱里 AppData\Temp 不可写 ⇒ gettempdir()
        # 会一路回退到 **cwd** ⇒ 降级目录落在仓库根、第一个项目文件就会弄脏 git 状态
        # （实测踩到 ✗✗✗）—— .lbcheck 那一档就是为它加的。
        for cand in (preferred,
                     Path.cwd() / ".lbcheck" / "lionforge",
                     Path(tempfile.gettempdir()) / "lionforge-platform"):
            try:
                (cand / "projects").mkdir(parents=True, exist_ok=True)
                self.dir = cand
                break
            except OSError as e:
                last_err = e
        if self.dir is None:
            raise last_err if last_err else RuntimeError("平台数据目录不可用")
        if self.dir != preferred:
            # 【文案要按落点说实话】.lbcheck 回退不是临时目录（重启不丢）；
            # 只有真落在 gettempdir() 里才配说"重启可能丢数据"。原来一律写
            # "临时目录、重启丢数据" —— 对 .lbcheck 而言是**不实的恐吓** ✗✗✗。
            in_tmp = tempfile.gettempdir() in str(self.dir) and ".lbcheck" not in str(self.dir)
            tail = ("（系统临时目录，机器重启可能丢数据）" if in_tmp
                    else "（回退目录；不在配置目录下，清理它会丢数据，重启不丢）")
            self.degraded = (f"首选数据目录不可写（{type(last_err).__name__}: {last_err}），"
                             f"已降级到 {self.dir}{tail}")
            print(f"[平台] ⚠ {self.degraded}", flush=True)
        self.projects_dir = self.dir / "projects"
        self.pool = ResourcePool(self.dir / "resources.json")
        self.store = ProjectStore(self.dir / "projects.json")
        # 账号 / 计费 / 独立 IP 池 —— 与项目数据同目录（跟随同一套降级链）
        self.auth = AuthStore(self.dir)
        self.billing = BillingStore(self.dir)
        self.ips = IpPool(self.dir)
        #: 运行中的部署进程 {pid: Popen}（平台活着才在；重启后进程丢失 → 详情标 degraded）
        self._procs: dict[str, subprocess.Popen[str]] = {}
        self._stop_flags: dict[str, threading.Event] = {}
        self._busy: set[str] = set()
        #: IP 租约（分配到"写进项目记录"之间的在途占用）—— 没有它，并发两个购买
        #: 会从池里拿到**同一个** IP（taken 只读记录、记录还没写 ✗✗✗）
        self._ip_leased: set[str] = set()
        #: 出站流量计数 {pid: bytes}（/serve 与独立IP直达的代发字节；周期扣费时落账）
        self._egress: dict[str, int] = {}
        #: 云端模型限流熔断器 + 同用户对话节流表（429 期间平台自己限流，不再撞云端）
        self._breaker = _Breaker(self.dir)   # 落盘持久化 —— 重启不清零
        self._last_chat_at: dict[str, float] = {}
        # 端口分配从 19000 起顺延，避开后端/适配器常用端口
        self._next_port = 19000
        self._reconcile()

    def _reconcile(self) -> None:
        """启动时自愈：上个进程留下的 building/testing/deploying 状态 = 已中断。
        后端一重启，那些状态就没有线程在推进（实测踩过：卡在 building 15 分钟
        但其实是旧进程的僵尸状态 ✗✗✗）—— 立刻标失败并给出可执行的下一步。"""
        for p in self.store.all():
            if p.get("status") in (ST_BUILDING, ST_TESTING, ST_DEPLOYING):
                self.store.update(p["id"], status=ST_FAILED,
                                  error="构建被后端重启中断（上个进程没跑完）——"
                                        "在下方对话框里说「继续」让 AI 从中断处接着做")
            elif p.get("status") == ST_LIVE and str(p.get("kind") or "") in ("", "unknown"):
                # 另一类僵尸：修复前的版本会把 unknown 标成 live（实测发生过 ✗✗✗）。
                self.store.update(p["id"], status=ST_FAILED,
                                  error="该记录来自旧版本的误判（没有产物却标了已上线）——重新构建或让 AI 重做")
        # 【僵尸配额清理】失败/中断的项目不该继续占资源池（实测：历史失败项目留下
        # 7 条 14 核/14GB 的死配额 ✗✗✗，池按物理机总量算，攒几次就建不了新项目）。
        # 规则：只有 live 项目保留配额；其余（failed/stopped/不存在）一律回收。
        live_ids = {p["id"] for p in self.store.all() if p.get("status") == ST_LIVE}
        for held in list(self.pool._alloc):
            if held not in live_ids:
                if self.pool.release(held):
                    print(f"[平台] 回收无主配额: {held}（项目非 live）", flush=True)
        # 【独立 IP 同步回收】失败/停止/不存在的项目不许攥着 IP —— 池占满会让新购买
        # 永远被拒（上线前抓到 ✗✗✗）；重新部署时 _ensure_quota 领回。
        for p in self.store.all():
            if p.get("ip") and p.get("status") != ST_LIVE:
                ip_held = p["ip"]
                self.store.update(p["id"], ip=None)
                print(f"[平台] 回收独立 IP: {ip_held}（项目 {p.get('status')}）", flush=True)

    # ---------------------------------------------------- 依赖定位
    def _deps(self) -> Any:
        from lionbox.api import deps                     # noqa: PLC0415 main 装配后才可用
        return deps

    def _agent(self) -> Any:
        return self._deps().agent_loop(self.ctx)

    def _review_hook(self) -> Any:
        try:
            import 工具                                    # noqa: PLC0415 闸门挂在工具模块上
            return getattr(工具, "REVIEW_HOOK", None)
        except Exception:                                   # noqa: BLE001
            return None

    # ---------------------------------------------------- 日志
    def log(self, pid: str, line: str) -> None:
        text = f"[{_now()}] {line}"
        print(f"[平台/{pid[:8]}] {line}", flush=True)
        try:
            p = self.projects_dir / pid / ".lionforge.log"
            p.parent.mkdir(parents=True, exist_ok=True)
            with open(p, "a", encoding="utf-8") as f:
                f.write(text + "\n")
        except OSError:
            pass

    def read_log(self, pid: str, tail: int = 400) -> str:
        p = self.projects_dir / pid / ".lionforge.log"
        try:
            lines = p.read_text(encoding="utf-8", errors="replace").splitlines()
            return "\n".join(lines[-tail:])
        except OSError:
            return ""

    # ---------------------------------------------------- Agent 执行（带自动放行）
    def _current_model(self) -> str | None:
        """当前该用的模型名 —— 与 ChatApi.saved_model 同语义：
        活适配器实例上的 model → 配置块(openai)的 model → 顶层 model → None。
        【为什么必须解析】process_message(model=None) 会让请求里 model 为 null，
        云端直接回 400 "Unsupported model"（首次实测就踩了这条 ✗✗✗）。
        """
        try:
            adapter = self.ctx.adapters().get_active_adapter()
            if adapter is not None:
                m = getattr(adapter, "model", None)
                if isinstance(m, str) and m.strip():
                    return m
                blk = self.ctx.cfg.get("openai")
                if isinstance(blk, dict) and str(blk.get("model") or "").strip():
                    return str(blk["model"])
            m = self.ctx.cfg.get("model")
            if isinstance(m, str) and m.strip():
                return m
        except Exception:                                   # noqa: BLE001 解析失败 → None
            pass
        return None

    def _agent_run(self, pid: str, session_id: str, message: str, thinking: str = "HIGH") -> str:
        """跑一轮 Agent；期间放行线程逐条 approve 待审改动。返回回复文本。"""
        stop = threading.Event()

        def approver() -> None:
            hook = self._review_hook()
            if hook is None:
                return
            while not stop.is_set():
                try:
                    for c in list(hook.list(session_id)):
                        cid = getattr(c, "id", None)
                        if cid:
                            hook.approve(cid)
                            self.log(pid, f"审核放行: {cid} {getattr(c, 'path', '')}")
                except Exception as e:                       # noqa: BLE001 放行线程不能影响主线程
                    self.log(pid, f"审核放行线程异常（忽略）: {type(e).__name__}: {e}")
                stop.wait(1.5)

        t = threading.Thread(target=approver, daemon=True, name=f"lionforge-approve-{pid[:8]}")
        t.start()
        try:
            reply = self._agent().process_message(session_id, message, "STANDARD",
                                                  thinking, self._current_model())
            return str(reply or "")
        finally:
            stop.set()
            t.join(timeout=5)
            # 【竞态终扫】模型**最后一轮**提交的待审改动，1.5s 轮询可能赶不上
            # （实测：C8562-1 卡在待审、AI 自己说"尚未落盘" ✗✗✗）。退出前同步扫几遍。
            for _ in range(6):
                try:
                    hook = self._review_hook()
                    pending = [c for c in (hook.list(session_id) if hook else [])
                               if getattr(c, "id", None)]
                except Exception:                           # noqa: BLE001
                    break
                if not pending:
                    break
                for c in pending:
                    try:
                        hook.approve(c.id)
                        self.log(pid, f"审核放行(终扫): {c.id} {getattr(c, 'path', '')}")
                    except Exception as e:                   # noqa: BLE001
                        self.log(pid, f"审核放行失败: {type(e).__name__}: {e}")
                time.sleep(0.4)

    # ---------------------------------------------------- 供给 → 构建
    def _provision_then_build(self, pid: str) -> None:
        """支付后的交付衔接：按实例模式先供给（vm=VBox 真机；host=主机进程模式），
        成功再进 Agent 构建管线；**供给失败 = 支付后没拿到机器 ⇒ 全额退款**。"""
        mode = os.environ.get("LION_INSTANCE_MODE", "vm").strip().lower()
        if mode != "vm":
            self.log(pid, "实例模式=host（主机进程模式；LION_INSTANCE_MODE=vm 切虚拟机）")
            self._build_pipeline(pid)
            return
        p = self.store.get(pid)
        if p is None or p.get("status") == ST_STOPPED:
            with LOCK:
                self._busy.discard(pid)
            return
        vbox = VBoxManager()
        ok, why = vbox.available()
        if not ok:
            self._vm_provision_failed(pid, why)
            return
        self.store.update(pid, status=ST_PROVISIONING)
        self.log(pid, f"开始创建虚拟机/安装 Windows（{why}）…")
        try:
            info = vbox.provision(f"lf-{pid}", int(p.get("cpu", 2)),
                                  int(p.get("memoryMb", 2048)), int(p.get("diskGb", 20)),
                                  log=lambda s: self.log(pid, s))
        except Exception as e:                               # noqa: BLE001
            self._vm_provision_failed(pid, f"{type(e).__name__}: {e}")
            return
        self.store.update(pid, vm=info.get("vm"), vmIp=info.get("ip"),
                          vmMode=info.get("mode"), status=ST_CREATED)
        self.log(pid, f"虚拟机就绪: {info}")
        self._build_pipeline(pid)

    def _refund_create(self, pid: str, why: str) -> int:
        """按最近一笔 create 正数扣款**全额退款**；没扣过/找不到 → 0。"""
        p = self.store.get(pid) or {}
        owner = str(p.get("owner") or "")
        cents = 0
        if owner and self.auth.enabled:
            for r in self.billing.list(user=owner, limit=200):
                if (r.get("kind") == "create" and r.get("projectId") == pid
                        and int(r.get("cents") or 0) > 0):
                    cents = int(r["cents"])
                    break
            if cents:
                self.auth.credit(owner, cents)
                self.billing.add("refund", owner, pid, str(p.get("spec") or ""), cents, why[:160])
        return cents

    def _vm_provision_failed(self, pid: str, why: str) -> None:
        """没拿到机器 ⇒ 全额退款 + 释放配额/IP + 失败。"""
        cents = self._refund_create(pid, f"虚拟机创建失败，全额退款：{why[:160]}")
        self.log(pid, f"❌ 虚拟机创建失败: {why}（退款 ¥{cents / 100:.2f}）")
        with LOCK:
            self._busy.discard(pid)
        self._release_quota(pid, "虚拟机创建失败")
        self._flush_egress(pid)
        self.store.update(pid, status=ST_FAILED,
                          error=f"虚拟机创建失败（{'已退款' if cents else '未扣过款'}）: {why[:400]}")

    # ---------------------------------------------------- 构建 → 自测 → 部署
    def _build_pipeline(self, pid: str) -> None:
        try:
            p = self.store.get(pid)
            if p is None:
                return
            src = self.projects_dir / pid
            session_id = p["sessionId"]
            # 【重建也要过配额闸】失败/停止过的项目配额与 IP 都已归还 —— 不领回就
            # 部署 = 绕过物理机总池记账（"重新构建"按钮会踩 ✗✗✗）。创建流程里配额
            # 已在购买时划走，这里重复登记是幂等的（allocate 剔除自身份额）。
            qerr = self._ensure_quota(pid)
            if qerr:
                self.log(pid, f"构建被拒：{qerr}")
                self.store.update(pid, status=ST_FAILED, error=qerr)
                return
            self.log(pid, "构建开始（Agent 接管；写文件会自动放行，产物由自测阶段把关）")
            self.store.update(pid, status=ST_BUILDING)
            prompt = self._build_prompt(p)
            t0 = time.time()
            # 心跳：Agent 那轮可能是几分钟的云端长响应，平台日志必须能看出"还活着"
            # （实测首版没有任何心跳，构建期查状态只能干等 ✗✗✗）
            beat_stop = threading.Event()

            def heartbeat() -> None:
                while not beat_stop.wait(30):
                    self.log(pid, f"构建中… 已 {int(time.time() - t0)} 秒（Agent 正在跑）")

            threading.Thread(target=heartbeat, daemon=True,
                             name=f"lionforge-beat-{pid[:8]}").start()
            try:
                reply = self._agent_run(pid, session_id, prompt)
            finally:
                beat_stop.set()
            self.log(pid, f"Agent 完成，耗时 {int(time.time() - t0)} 秒")
            # 【停止权优先】用户在构建期间点了停止 ⇒ 不进自测/部署（状态保持已停止）
            if not self._still_running(pid):
                self.log(pid, "构建期间被用户停止（跳过自测与部署）")
                return
            self.store.update(pid, status=ST_TESTING, buildReply=reply[:4000])
            self._test_and_deploy(pid, src)
        except Exception as e:                               # noqa: BLE001 平台不许静默失败
            self.log(pid, f"❌ 管线异常: {type(e).__name__}: {e}")
            self._release_quota(pid, "管线异常")
            if self._still_running(pid):
                self.store.update(pid, status=ST_FAILED, error=f"{type(e).__name__}: {e}")
        finally:
            with LOCK:
                self._busy.discard(pid)

    def _build_prompt(self, p: dict[str, Any]) -> str:
        src = self.projects_dir / p["id"]
        return (
            "你是 TigerForge 平台的构建 Agent，在**当前工作区目录**（就是本项目目录）里交付一个完整可运行的项目。\n"
            f"【项目名】{p['name']}\n"
            f"【项目绝对路径】{src} —— 所有文件的创建/修改/读取一律用这个绝对路径开头，"
            "不要写到任何别的目录（比如仓库根）。\n"
            f"【资源配额】CPU {p['cpu']} 核 / 内存 {p['memoryMb']} MB / 磁盘 {p['diskGb']} GB —— "
            "程序本身要尊重这些限制（别引入超大依赖/权重；服务默认监听 {PORT} 环境变量指定的端口）。\n"
            f"【用户需求】{p['prompt']}\n"
            "【交付要求（必须全部做到）】\n"
            "1. 在本目录里创建完整源码；入口清晰（网页应用给 server 或纯静态入口）。\n"
            "2. 写 README.md：怎么启动、目录结构、技术选型。\n"
            "3. **必须真自测**：真的把它启动起来/跑起来，用命令验证关键路径"
            "（服务类用 HTTP 请求验证状态码与页面标题；脚本类直接运行断言输出），"
            "把「执行的命令 + 真实输出」写进最后的结论。\n"
            "4. 自测不通过就继续修，修到通过为止；若确实修不通，结论里如实写「未通过 + 原因」。\n"
            "5. 若产物是网页应用，额外把**离线静态副本**放到 dist/client/ 下并打成 zip"
            "（Windows PowerShell 可用 Compress-Archive）——这是给用户的下载包。\n"
            "6. 最后用一段话总结：做了什么、自测结果（含关键命令输出）、怎么运行。\n"
            "先想清楚再动手；过程中不需要反问我，自己推进。"
        )

    # ---------------------------------------------------- 自测 + 部署
    def _classify(self, src: Path) -> str:
        pj = src / "package.json"
        has_web = (src / "public" / "index.html").is_file() or (src / "index.html").is_file()
        script_start = False
        try:
            script_start = bool(json.loads(pj.read_text(encoding="utf-8")).get("scripts", {}).get("start"))
        except Exception:                                   # noqa: BLE001
            pass
        has_web = has_web or script_start or (src / "server.js").is_file() or (src / "app.js").is_file()
        has_client = False
        for d in ("dist", "build", "out", "release"):
            dd = src / d
            if dd.is_dir() and any(dd.rglob("*.exe")):
                has_client = True
        if list(src.glob("*.exe")) or list(src.glob("*.msi")):
            has_client = True
        if has_web and has_client:
            return "three-tier"
        if has_web:
            return "web"
        if has_client:
            return "client"
        return "unknown"

    def _pick_port(self) -> int:
        """挑一个**当前空闲**的端口。
        【为什么不能单调 +1 就返回】原实现从不 bind 验证 ⇒ 19000+ 里被别的服务/
        别的项目占着的端口照样会被发出去 ⇒ 新进程绑不上、探活探到**别人的服务**
        当成自己部署成功的证据 ✗✗✗（连挑 50 次都不空 → 返回 0，调用方按静态站处理）。"""
        for _ in range(50):
            port = self._next_port
            self._next_port += 1
            if self._next_port > 19999:
                self._next_port = 19000
            if self._port_free(port):
                return port
        return 0

    def _start_server(self, pid: str, src: Path, port: int) -> subprocess.Popen[str] | None:
        """起网页服务（优先 bun，其次 node/npm）；起不来返回 None（当静态站处理）。"""
        env = dict(os.environ)
        env["PORT"] = str(port)
        env["HOST"] = "127.0.0.1"
        p = self.store.get(pid) or {}
        # 带宽是**分配值**：下发给应用让它自限速（服务器端真限速在网关/容器做，
        # 进程级限速做不到 —— 详情页如实说明，不假装）。
        if p.get("bandwidthMb"):
            env["LIMIT_BANDWIDTH_MBPS"] = str(p["bandwidthMb"])
        cmd: list[str] | None = None
        try:
            pj = json.loads((src / "package.json").read_text(encoding="utf-8"))
        except Exception:                                   # noqa: BLE001
            pj = {}
        bun = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bun.exe")
        if not os.path.isfile(bun):
            bun = shutil.which("bun") or ""
        node = shutil.which("node") or ""
        entry = next((e for e in ("server.js", "app.js", "index.js") if (src / e).is_file()), None)
        if pj.get("scripts", {}).get("start"):
            if bun:
                cmd = [bun, "run", "start"]
            elif node:
                # start 脚本但没有 npm/bun 可跑 ⇒ 直接点名可执行入口，别白白退化成
                # 静态站（第一版只认 server.js，index.js/app.js 全漏 ✗✗✗）
                e2 = next((e for e in ("server.js", "index.js", "app.js")
                           if (src / e).is_file()), None)
                cmd = [node, e2] if e2 else None
        elif entry:
            runner = bun or node
            if runner:
                cmd = [runner, entry]
        if cmd is None:
            self.log(pid, "未找到可启动的服务入口 → 按静态站部署")
            return None
        logf = open(self.projects_dir / pid / ".server.log", "a", encoding="utf-8")
        proc = subprocess.Popen(cmd, cwd=str(src), env=env, stdout=logf, stderr=logf,
                                creationflags=CREATE_NO_WINDOW)
        # 【限制必须传项目配额】第一版写死 apply_process_limits(pid, 0, 0) ✗✗✗：
        # cpu=0 被夹成 1 核、mem=0 变成"0 字节上限"，配额完全没生效（实测亲和 0x1≠0x3）。
        warns = apply_process_limits(proc.pid, int(p.get("cpu", 1)), int(p.get("memoryMb", 1024)))
        self.log(pid, f"服务已启动: {' '.join(cmd)} pid={proc.pid} port={port}"
                      + (f"  ⚠ 限制未生效: {'; '.join(warns)}" if warns else "  ✓ 资源限制已生效"))
        return proc

    def _probe(self, port: int) -> tuple[bool, int, str]:
        """探测 http://127.0.0.1:port/；返回 (通?, 状态码, 页面标题)。"""
        deadline = time.time() + PROBE_TIMEOUT
        last = ""
        while time.time() < deadline:
            try:
                req = urllib.request.Request(f"http://127.0.0.1:{port}/")
                with urllib.request.urlopen(req, timeout=3) as r:
                    body = r.read(200000).decode("utf-8", "replace")
                    title = re.search(r"<title[^>]*>(.*?)</title>", body, re.S | re.I)
                    return True, int(r.status), (title.group(1).strip()[:80] if title else "")
            except urllib.error.HTTPError as e:              # HTTP 错误也算"服务活着"
                return True, int(e.code), ""
            except Exception as e:                           # noqa: BLE001 连接拒绝 → 继续等
                last = f"{type(e).__name__}"
                time.sleep(1.0)
        return False, 0, last

    def _zip_client(self, pid: str, src: Path) -> list[str]:
        """把客户端产物/离线副本打成 zip；返回产物文件名列表。"""
        out_dir = self.projects_dir / pid / ".lionforge"
        out_dir.mkdir(parents=True, exist_ok=True)
        made: list[str] = []
        for d in ("dist/client", "dist", "build", "out", "release"):
            dd = src / d
            if not dd.is_dir():
                continue
            if d == "dist/client":
                zp = out_dir / f"{pid}-client.zip"
                with zipfile.ZipFile(zp, "w", zipfile.ZIP_DEFLATED) as z:
                    for f in dd.rglob("*"):
                        if f.is_file():
                            z.write(f, f.relative_to(dd).as_posix())
                made.append(zp.name)
            # 打包目录里的安装器/可执行（客户端产物常见的落点）
            for f in list(dd.rglob("*.exe")) + list(dd.rglob("*.msi")):
                dst = out_dir / f.name
                if not dst.exists():
                    shutil.copy2(f, dst)
                made.append(dst.name)
        for f in list(src.glob("*.exe")) + list(src.glob("*.msi")):
            dst = out_dir / f.name
            shutil.copy2(f, dst)
            made.append(dst.name)
        # 无论有没有客户端产物，都给一份源码 zip（下载页总要有东西可下）
        zp = out_dir / f"{pid}-source.zip"
        with zipfile.ZipFile(zp, "w", zipfile.ZIP_DEFLATED) as z:
            for f in src.rglob("*"):
                if f.is_file() and ".lionforge" not in f.parts and "node_modules" not in f.parts:
                    z.write(f, f.relative_to(src).as_posix())
        made.append(zp.name)
        return made

    def _stop_proc(self, pid: str) -> None:
        """停掉本项目已登记的服务进程（stop / redeploy / 探活失败前都要先走它）。
        【为什么抽出来】redeploy 原来直接 _start_server ⇒ 旧进程不被杀、一直占着端口，
        新进程绑不上端口死掉、`_procs` 被覆盖成死进程 ⇒ 之后 stop 杀的是死进程、
        老进程变永久孤儿（实测推演 ✗✗✗）。统一走这里就不会漏杀。"""
        proc = self._procs.pop(pid, None)
        if proc is None:
            return
        try:
            proc.terminate()
            proc.wait(timeout=6)
        except Exception:                                   # noqa: BLE001
            try:
                proc.kill()
            except Exception:                               # noqa: BLE001
                pass

    @staticmethod
    def _port_free(port: int) -> bool:
        """端口当前是否空闲（bind 一次即测，随后释放）。"""
        try:
            with socket.socket() as s:
                s.bind(("127.0.0.1", int(port)))
            return True
        except OSError:
            return False

    def _test_and_deploy(self, pid: str, src: Path) -> None:
        p = self.store.get(pid)
        if p is None:
            return
        # 【停止权优先】构建/自测期间用户点了"停止" ⇒ 后续状态一律不写（否则
        # stop 会被构建线程改回 testing/live 并把服务真的拉起来 ✗✗✗）。
        if p.get("status") == ST_STOPPED:
            self.log(pid, "项目已被停止，跳过部署")
            return
        kind = self._classify(src)
        self.log(pid, f"自测开始：产物形态 = {kind}")
        self.store.update(pid, status=ST_TESTING, kind=kind)
        web_url = None
        test = {"kind": kind, "ok": False, "http": None, "title": None, "note": ""}
        if kind in ("web", "three-tier"):
            # 重部署复用旧端口，但**必须先确认它空闲** —— 单调 +1 或旧进程没死时
            # 挑到被占端口 ⇒ 新进程绑不上、探活探到**别人的服务**当自己的 ✗✗✗。
            port = int(p.get("port") or 0)
            if not port or not self._port_free(port):
                port = self._pick_port()
            proc = self._start_server(pid, src, port) if port else None
            if proc is not None:
                self._procs[pid] = proc
                ok, code, title = self._probe(port)
                test.update(ok=ok, http=code, title=title)
                self.log(pid, f"自测探活: ok={ok} http={code} title={title!r}")
                if ok:
                    web_url = f"/serve/{pid}/"
                    self.store.update(pid, port=port, webUrl=web_url)
                else:
                    self.log(pid, "❌ 自测未通过：服务起不来或探活超时（server.log 有明细）")
                    self._stop_proc(pid)        # 半死进程不许留着占资源（探活失败即回收）
            else:
                if not port:
                    self.log(pid, "⚠ 无可用端口（19000-19999 全占）→ 按静态站处理")
                # 静态站：只要目录里有 html 就算通过
                html = src / "public" / "index.html"
                if not html.is_file():
                    html = src / "index.html"
                test.update(ok=html.is_file(), note="静态站" if html.is_file() else "无 HTML 入口")
                self.log(pid, f"静态站判定: {'通过' if test['ok'] else '❌ 没有 index.html'}")
                if test["ok"]:
                    web_url = f"/serve/{pid}/"
                    self.store.update(pid, webUrl=web_url)
        # 客户端产物 → zip + 下载页（web-only 项目也会有源码 zip，下载页始终可用）
        artifacts = self._zip_client(pid, src)
        self.store.update(pid, artifacts=artifacts, dlUrl=f"/dl/{pid}/")
        self.log(pid, f"下载包就绪: {', '.join(artifacts)}  → /dl/{pid}/")
        # 磁盘配额核对（如实报告，不装死）
        used_mb = sum(f.stat().st_size for f in src.rglob("*") if f.is_file()) // (1024 * 1024)
        over = used_mb > int(p.get("diskGb", 0)) * 1024
        self.log(pid, f"磁盘占用 {used_mb} MB / 配额 {p.get('diskGb')} GB" + ("（⚠ 超配额）" if over else ""))
        if not test["ok"] and kind in ("web", "three-tier"):
            self._release_quota(pid, "自测未通过")
            self.store.update(pid, status=ST_FAILED, test=test,
                              error="自测未通过（服务探活失败）——产物保留在项目目录，可让 AI 继续修")
            return
        if kind == "unknown":
            # 【没有任何可识别产物 = 构建失败】产物形态认不出来就必须算失败，
            # 不许用"部署完成"骗人（第一天实测就踩过：空目录被标 live ✗✗✗）。
            # 【零产物 + 模型调用失败 = 服务器侧没交付 ⇒ 全额退款】429/401/网络把
            # Agent 打死在第一轮（实测 14 秒零产物、用户已付两笔 ¥23 ✗✗✗✗✗）——
            # 这钱不该由用户承担，原路退回并把下一步写进错误文案。
            p_now = self.store.get(pid) or {}
            model_dead = "模型调用失败" in str(p_now.get("buildReply") or "")
            if model_dead:
                self._breaker.fail()   # 熔断开闸：期间购买/重建/对话全部自己限流
            cents = 0
            if model_dead:
                cents = self._refund_create(
                    pid, "构建零产物且模型调用失败（服务器侧额度/网络），全额退款")
                self.log(pid, f"模型调用失败导致零产物 → 全额退款 ¥{cents / 100:.2f}")
            self._release_quota(pid, "没有可识别产物")
            if model_dead:
                err_text = ("Agent 零产物（模型调用失败"
                            + ("，已全额退款；配额/网络恢复后点「重新构建」）" if cents
                               else "，未扣过款）"))
            else:
                err_text = ("Agent 没有产出可识别的产物（看「Agent 结论」；"
                            "可对话或点「重新构建」重做）")
            self.store.update(pid, status=ST_FAILED, test=test, error=err_text)
            return
        # 【停止权优先】最终状态写入前再核一次：部署期间用户点了停止就不许改写成 live
        if not self._still_running(pid):
            self._release_quota(pid, "部署期间被停止")
            self.log(pid, "部署被用户停止打断（不写 live、不保留配额）")
            return
        self.store.update(pid, status=ST_LIVE, test=test)
        self.log(pid, f"✅ 部署完成：网页={web_url or '（无）'} 下载页=/dl/{pid}/")
        # 配额保留到显式 stop/失败释放 —— 见 stop_project 与 _release_quota

    def _still_running(self, pid: str) -> bool:
        cur = self.store.get(pid)
        return cur is not None and cur.get("status") != ST_STOPPED

    def _release_quota(self, pid: str, why: str) -> None:
        """失败/中断即释放配额 + **独立 IP 一并归还**。

        配额：原来只有 stop 释放 ✗✗✗（连续失败几次就把物理机总池占满）。
        IP：生命周期必须与配额**同进退** —— 失败/停止的实例若永远攥着 IP，
        池子占满后所有新购买都被"IP 池已占满"卡死（上线前抓到的设计缺陷 ✗✗✗）。
        重新部署时由 `_ensure_quota` 一并领回。"""
        p = self.store.get(pid)
        if p is not None and p.get("ip"):
            self.store.update(pid, ip=None)
            self.log(pid, f"独立 IP {p['ip']} 已归还 IP 池（{why}）")
        if self.pool.release(pid):
            self.log(pid, f"资源配额已释放（{why}）")

    def _ensure_quota(self, pid: str) -> str | None:
        """重新部署前确保配额在册（失败已释放过 / 后端重启后池与状态不同步）；
        划不到就如实返回原因（不许"没配额也照样起服务"绕过总池）。
        独立 IP 同步**补领**（失败/停止时已归还；池满则如实记日志继续部署 ——
        交付优先于地址，购买时那道"分不到就不卖"的硬闸只在购买时生效）。"""
        p = self.store.get(pid) or {}
        err = self.pool.allocate(pid, int(p.get("cpu", 1)), int(p.get("memoryMb", 1024)),
                                 int(p.get("diskGb", 20)), int(p.get("bandwidthMb", 0)))
        if err:
            return err
        if not p.get("ip") and self.ips.pool:
            ip2 = self._take_ip()
            if ip2:
                self.store.update(pid, ip=ip2)
                self._lease_owned(ip2)          # 记录写上了，租约转正退场
                self.log(pid, f"独立 IP 已重新分配: {ip2}")
            else:
                self.log(pid, "⚠ IP 池已满，本次部署未分到独立 IP（购买硬闸不受影响）")
        return None

    # ---------------------------------------------------- 鉴权 / 独立IP / 计费
    def _json(self, data: Any, status: int = 200,
              headers: dict[str, str] | None = None) -> Any:
        """带 headers 的 JSON 响应（登录要 Set-Cookie —— Response.json 不收 headers）。"""
        return self.Response(json.dumps(data, ensure_ascii=False).encode("utf-8"), status,
                             "application/json; charset=utf-8", headers or {})

    def _cookie_token(self, req: Any) -> str | None:
        m = re.search(r"(?:^|;\s*)lion_sid=([0-9a-f]+)", req.headers.get("cookie") or "")
        return m.group(1) if m else None

    def user_of(self, req: Any) -> str | None:
        return self.auth.user_of(self._cookie_token(req))

    def _owner_ok(self, req: Any, project: dict[str, Any] | None) -> bool:
        """这个请求者能不能动这个项目（鉴权关闭=都能；开管理员=都能；否则必须是 owner）。"""
        if project is None:
            return False
        if not self.auth.enabled:
            return True
        u = self.user_of(req)
        if u is None:
            return False
        if self.auth.is_admin(u):
            return True
        return (project.get("owner") or "") == u

    def _require_admin(self, req: Any) -> Any:
        """None=放行；否则 403 响应。"""
        if not self.auth.enabled:
            return self._json({"success": False, "error": "鉴权未启用（先创建首个账号）"}, 403)
        if not self.auth.is_admin(self.user_of(req)):
            return self._json({"success": False, "error": "需要管理员"}, 403)
        return None

    def _take_ip(self) -> str | None:
        """从池里认领一个独立 IP（上锁：记录 ∪ 租约 = 已占用）。"""
        with LOCK:
            taken = {str(q.get("ip")) for q in self.store.all() if q.get("ip")}
            taken |= self._ip_leased
            ip = self.ips.free(taken)
            if ip:
                self._ip_leased.add(ip)
            return ip

    def _lease_owned(self, ip: str | None) -> None:
        """认领物已写进项目记录 → 租约转正（由记录接管占用判定）。"""
        if ip:
            with LOCK:
                self._ip_leased.discard(ip)

    def _add_egress(self, pid: str, n: int) -> None:
        """出站字节计数（内存攒着，扣费/详情/停止时落账 —— 每请求都写盘太重 ✗✗✗）。"""
        with LOCK:
            self._egress[pid] = self._egress.get(pid, 0) + max(0, int(n))

    def _flush_egress(self, pid: str) -> None:
        with LOCK:
            n = self._egress.pop(pid, 0)
        if n:
            p = self.store.get(pid)
            if p is not None:
                self.store.update(pid, egressBytes=int(p.get("egressBytes") or 0) + n)

    def _archive_chat(self, pid: str, session_id: str, owner: str,
                      user_msg: str, reply: str) -> None:
        """对话**永久存储**（用户要求）：① 项目内 chat.jsonl —— 永远写（零依赖、
        跟着实例走、重启/换机都在）② MySQL lion_messages —— 配了 DSN 才写穿
        （内容走 _sql_str 字面量转义；表启动自动建）。两份都是"用户看到的那轮对话"。
        写失败只出声不挡聊天（对话本身已在历史存储里，这是归档层）。"""
        rows = (("user", user_msg), ("assistant", reply))
        try:
            fdir = self.projects_dir / pid / ".lionforge"
            fdir.mkdir(parents=True, exist_ok=True)
            with open(fdir / "chat.jsonl", "a", encoding="utf-8") as f:
                for role, text in rows:
                    f.write(json.dumps({"at": _now(), "session": session_id, "role": role,
                                        "text": text[:_MSG_CAP]},
                                       ensure_ascii=False) + "\n")
        except OSError as e:
            self.log(pid, f"⚠ 对话归档(chat.jsonl)写入失败: {type(e).__name__}: {e}")
        if self.auth.account_db.startswith("mysql:"):
            for role, text in rows:
                ok = self.auth._my_run(
                    "INSERT INTO lion_messages (session_id, project_id, owner, role, "
                    "content, created_at) VALUES ('%s','%s','%s','%s',%s,'%s')"
                    % (session_id, pid, owner or "", role, _sql_str(text), _now()))
                if ok is None:
                    self.log(pid, "⚠ 对话入库(lion_messages)失败（已有告警；jsonl 仍在）")
                    break

    def dispatch_deployed(self, pid: str, rest: str) -> Any:
        """项目部署出口的**唯一**分发实现：先代理活进程，再静态站兜底。
        `/serve` 处理器与"按独立 IP 直达"的进门门共用这一份（两条入口一种行为 ✗✗✗
        ——原来 serve 里内联一份，加 IP 直达时差点复制第二份、以后必漂移）。"""
        p = self.store.get(pid)
        if p is None:
            return self._json({"ok": False, "error": "项目不存在"}, 404)
        proc = self._procs.get(pid)
        src = self.projects_dir / pid
        if proc is not None and p.get("port"):
            try:
                url = f"http://127.0.0.1:{p['port']}/{urllib.parse.quote(rest)}"
                with urllib.request.urlopen(url, timeout=30) as r:
                    body = r.read()
                    ctype = r.headers.get("Content-Type") or "text/html; charset=utf-8"
                self._add_egress(pid, len(body))   # 出站流量计费口径：平台代发的响应字节
                return self.Response(body, content_type=ctype)
            except urllib.error.HTTPError as e:
                err_body = e.read()
                self._add_egress(pid, len(err_body))   # 错误响应也是平台代发的字节（口径一致）
                return self.Response(err_body, status=int(e.code))
            except Exception as e:                           # noqa: BLE001
                return self._json({"ok": False, "error": f"代理失败: {e}"}, 502)
        # 静态站兜底
        root = src / "public"
        if not root.is_dir():
            root = src
        rel = urllib.parse.unquote(rest) or "index.html"
        target = (root / rel).resolve()
        try:
            target.relative_to(root.resolve())
        except ValueError:
            return self._json({"ok": False, "error": "非法路径"}, 400)
        if target.is_dir():
            target = target / "index.html"
        if not target.is_file():
            return self._json({"ok": False, "error": "文件不存在"}, 404)
        ctype = MIME.get(target.suffix.lower(), "application/octet-stream")
        data = target.read_bytes()
        self._add_egress(pid, len(data))
        return self.Response(data, content_type=ctype)

    #: 租户（非管理员）可碰的前缀。**除此之外一律 403** —— 攻击者视角这条是命门：
    #: 鉴权只查"登录过"的话，普通租户能直接打 /api/chat/adapter/config 与
    #: /api/runtime/mode（改全局模型配置=截所有人的构建流量 ✗✗✗，上一轮在 create
    #: 里堵了，正门却还开着）、/api/filesystem（枚举服务器）、/api/workspaces+
    #: /api/sessions（换工作区=绕开全部隔离）、/api/chat|stream（绕过计费直连 Agent
    #: 烧钱）、/api/context、/api/plugins、/api/skills、/api/changes、/api/tools…
    _TENANT_OK = ("/platform", "/api/auth/", "/api/platform/", "/api/models/",
                  "/serve/", "/dl/", "/favicon")

    def http_gate(self, req: Any) -> Any:
        """注册进 `_HTTP_GATES` 的进门门（跑在租户锁定与路由**之前**）。

        ① Host 命中某 live 实例的专属 IP ⇒ 直接代理给它的应用（自己 IP 自己说了算）
        ② 登录鉴权（users.json 有账号才启用）：未登录 → 401
        ③ **角色面**：普通租户只许 `_TENANT_OK` 平台面，运维接口 403；
           管理员放行（仍受 LION_TENANT_LOCK 约束）。
        公开面（免登录）：/platform（页面自管登录态）、/api/auth/*、favicon、
        /serve /dl（已部署出口 = 公开链接，与真实部署语义一致）。
        """
        path = req.path
        # ① 独立 IP 直达
        host = (req.headers.get("host") or "").split(":")[0].strip()
        if host and path != "/platform" and not path.startswith("/api/auth/"):
            for p in self.store.all():
                if p.get("ip") == host and p.get("status") == ST_LIVE:
                    return self.dispatch_deployed(p["id"], urllib.parse.unquote(path.lstrip("/")))
        # ② 鉴权
        if not self.auth.enabled:
            return None
        if path in ("/platform", "/admin") or path.startswith(("/api/auth/", "/favicon")):
            return None
        if path.startswith(("/serve/", "/dl/")):
            return None
        u = self.user_of(req)
        if u is None:
            return self._json({"success": False, "error": "未登录或登录已过期"}, 401)
        # ③ 角色面（租户 = 只有平台面）
        if not self.auth.is_admin(u) and not path.startswith(self._TENANT_OK):
            return self._json({"success": False,
                               "error": "租户账号无权访问运维接口（仅管理员可用）"}, 403)
        return None

    def _tick_billing(self, force_periods: float | None = None,
                      now: float | None = None) -> dict[str, Any]:
        """周期扣费（心跳每小时一轮；鉴权启用才动钱）。

        · 常规：paidUntil 到期 → 扣**下一期**（算力月租/包年 + 分项×期数 +
          未结出站流量），成功则 paidUntil=now+周期、流量结转标记推进。
        · force_periods=K：管理端补扣 K 期（1..12），同样并入未结流量。
        · 余额不够 → **停机不欠账**（未结流量随停机免单，账单写明）。
        · 参数越界/非数字拒绝 —— 负数会把 paidUntil 回拨 ⇒ 下轮心跳立刻再扣
          （脏状态 ✗✗✗），必须校验。
        """
        if force_periods is not None:
            try:
                fp = float(force_periods)
            except (TypeError, ValueError):
                return {"error": "补扣期数必须是数字"}
            if not (1 <= fp <= 12):
                return {"error": "补扣期数必须在 1..12 之间"}
        now = time.time() if now is None else now
        charged: list[str] = []
        stopped: list[str] = []
        if not self.auth.enabled:
            return {"charged": [], "stopped": [], "note": "鉴权未启用（开放模式不计费）"}
        for p in self.store.all():
            if p.get("status") != ST_LIVE or not p.get("owner"):
                continue
            if force_periods is None and float(p.get("paidUntil") or 0) > now:
                continue
            # 流量先落账（/serve 与独立IP直达的代发字节在内存里攒着）
            self._flush_egress(p["id"])
            p = self.store.get(p["id"]) or p
            delta = max(0, int(p.get("egressBytes") or 0) - int(p.get("egressBilledBytes") or 0))
            cycle = "year" if p.get("cycle") == "year" else "month"
            k = float(force_periods) if force_periods is not None else 1.0
            one = period_total_cents(str(p.get("spec") or ""), int(p.get("cpu", 1)),
                                     int(p.get("memoryMb", 1024)), int(p.get("diskGb", 20)),
                                     bool(p.get("ip")), cycle, egress_bytes=delta)
            cents = max(1, int(round(one * k)))
            owner = str(p.get("owner"))
            label = "包年" if cycle == "year" else "月租"
            if self.auth.charge(owner, cents):
                upd: dict[str, Any] = {"paidUntil": now + CYCLE_SECONDS[cycle] * k}
                if delta:
                    upd["egressBilledBytes"] = int(p.get("egressBytes") or 0)
                self.store.update(p["id"], **upd)
                self.billing.add("period", owner, p["id"], str(p.get("spec") or ""), cents,
                                 f"{label}续期 {k:g} 期"
                                 + ("（管理端补扣）" if force_periods is not None else "")
                                 + (f"；含未结流量 {delta / (1024 ** 3):.2f}GB" if delta else ""))
                charged.append(p["id"])
                self.log(p["id"], f"{label}续期扣费 ¥{cents / 100:.2f}（{k:g} 期）"
                                  + (f" 含流量 {delta / (1024 ** 3):.2f}GB" if delta else ""))
            else:
                note = f"余额不足（需 {cents} 分），停机不欠账"
                if delta:
                    note += f"；未结流量 {delta / (1024 ** 3):.2f} GB 随停机免单"
                    # 【免单要兑现】把流量水位推进到当前 —— 否则日后重启实例会把
                    # 这笔"已宣告免单"的流量又收一遍 ✗✗✗（账实不符）
                    self.store.update(p["id"], egressBilledBytes=int(p.get("egressBytes") or 0))
                self.billing.add("stop-nobalance", owner, p["id"], str(p.get("spec") or ""), 0,
                                 note)
                self.log(p["id"], f"余额不足（需 {cents} 分）→ 停机不欠账")
                self.stop_project(p["id"])
                stopped.append(p["id"])
        return {"charged": charged, "stopped": stopped}

    # ---------------------------------------------------- API 处理
    def info(self) -> dict[str, Any]:
        specs = physical_specs()
        used = self.pool.used()
        return {"name": PLATFORM_NAME, "tag": PLATFORM_TAG, "physical": specs, "used": used,
                # 【实例规格预设】用户买的是档位不是散核 —— 与云厂商一致：
                # 1C1G / 2C2G / 4C8G / 8C16G；带宽 5-100M；硬盘 10-100G。
                "options": {"specs": ["1C1G", "2C2G", "4C8G", "8C16G"],
                            "bandwidthMb": [5, 10, 20, 50, 100],
                            "diskGb": [10, 20, 50, 100]},
                "note": "实例=工作区+配额（CPU亲和/Job内存/磁盘记账，进程级隔离）；"
                        "带宽为分配值（真限速在网关/容器，见详情）；真虚拟机/容器为部署选项",
                # 租户锁定三态（页面按它分绿/灰/黄）: 开 / 显式关 / 未配置
                "tenantLock": os.environ.get("LION_TENANT_LOCK") == "1",
                "lockSet": os.environ.get("LION_TENANT_LOCK") is not None,
                # 数据目录降级原因（空=正常）：非空时页面顶栏亮红条，不静默。
                "degraded": self.degraded,
                # 页面要用：价格表（新口径：月租/包年/分项/流量）、IP 池、鉴权、实例模式
                "pricing": {"month": BASE_MONTH_CENTS, "year": BASE_YEAR_CENTS,
                            "ipMonth": IP_MONTH_CENTS, "diskGbMonth": DISK_GB_MONTH_CENTS,
                            "trafficGb": TRAFFIC_GB_CENTS},
                "instanceMode": os.environ.get("LION_INSTANCE_MODE", "vm"),
                "vbox": _vbox_status(),
                "accountDb": self.auth.account_db,
                "ipPool": {"configured": bool(self.ips.pool), "count": len(self.ips.pool)},
                "authEnabled": self.auth.enabled}

    def create_project(self, body: dict[str, Any], user: str | None = None) -> dict[str, Any]:
        name = str(body.get("name") or "").strip() or "未命名项目"
        prompt = str(body.get("prompt") or "").strip()
        if not prompt:
            return {"ok": False, "error": "缺少「开始提示词」——要告诉 AI 做什么"}
        # 【配额预检（省钱闸）】熔断器开着 = 云端 429 刚失败过 → 直接拒买：否则就是
        # 扣款→14秒死→退款 的空转（用户 2026-10-22 一晚连点4次 ✗✗✗✗✗）。
        if self._breaker.tripped():
            return {"ok": False, "error": self._breaker.msg()}
        # 【实例规格】买档位不买散核：1C1G/2C2G/4C8G/8C16G；带宽 5-100M；硬盘 10-100G。
        # 兼容：没给 spec 时退回旧的 cpu/memoryMb 字段（API 老调用还能用）。
        # 【校验顺序的坑，实测踩过】第一版在 else 分支里把 spec **重写**成默认 2C2G，
        # 于是"未知规格"检查永远见到的是合法串 —— 传 99C99G 竟然 200 通过、静默变
        # 2C2G ✗✗✗✗✗。规格字符串必须**先解析先校验**，最后才允许兼容回退。
        spec = str(body.get("spec") or "").upper().strip()
        spec_map = {"1C1G": (1, 1024), "2C2G": (2, 2048), "4C8G": (4, 8192), "8C16G": (8, 16384)}
        try:
            bw = int(body.get("bandwidthMb") or 10)
            disk = int(body.get("diskGb") or 20)
        except (TypeError, ValueError):
            return {"ok": False, "error": "带宽/硬盘必须是数字"}
        if spec in spec_map:
            cpu, mem = spec_map[spec]
        elif spec:
            m = re.fullmatch(r"(\d+)C(\d+)G", spec)
            if not m:
                return {"ok": False, "error": f"未知实例规格：{spec}（可选 1C1G/2C2G/4C8G/8C16G）"}
            cpu, mem = int(m.group(1)), int(m.group(2)) * 1024
        else:
            try:
                cpu = int(body.get("cpu") or 2)
                mem = int(body.get("memoryMb") or 2048)
            except (TypeError, ValueError):
                return {"ok": False, "error": "资源参数必须是数字"}
            spec = f"{cpu}C{mem // 1024}G"
        specs = physical_specs()
        if cpu < 1 or cpu > specs["cores"]:
            return {"ok": False, "error": f"规格 {spec} 超出物理机：只有 {specs['cores']} 核"}
        if mem < 256 or mem > specs["ramMb"]:
            return {"ok": False, "error": f"规格 {spec} 超出物理机：只有 {specs['ramMb']} MB 内存"}
        if bw < 5 or bw > 100:
            return {"ok": False, "error": "带宽必须在 5..100 M"}
        if disk < 10 or disk > 100:
            return {"ok": False, "error": "硬盘必须在 10..100 G"}
        # 计费周期（支付页选月租/包年；包年 8 折仅算力）—— 在扣费前先校验
        cycle = str(body.get("cycle") or "month").strip().lower()
        if cycle in ("y", "yr", "year", "12", "年", "annual", "包年"):
            cycle = "year"
        elif cycle in ("", "m", "mo", "month", "1", "月", "月租", "monthly"):
            cycle = "month"
        else:
            return {"ok": False, "error": "计费周期只能是 month（月租）或 year（包年）"}
        pid = datetime.now().strftime("p%Y%m%d%H%M%S") + os.urandom(3).hex()
        src = self.projects_dir / pid
        src.mkdir(parents=True, exist_ok=True)
        err = self.pool.allocate(pid, cpu, mem, disk, bw)
        if err:
            shutil.rmtree(src, ignore_errors=True)
            return {"ok": False, "error": err}

        # AI API：给了就写进配置并重指适配器（与 /api/chat/adapter/config 同语义：掩码=没改）
        # 【自定义端点 = 管理员专用】非管理员的 aiApi（含仅换模型名）会写进**全局**
        # 配置 ⇒ 一个租户把 baseUrl 指到自己的服务器，所有人的构建流量都被他截 ✗✗✗
        # （多租户下的真实横向风险）。租户只用服务端统一配置的模型。
        ai = body.get("aiApi") or {}
        if self.auth.enabled and not self.auth.is_admin(user):
            ai = {}
        ai_used = {"baseUrl": "", "model": "", "hasKey": False}
        if isinstance(ai, dict) and any([ai.get("baseUrl"), ai.get("apiKey"), ai.get("model")]):
            try:
                cfg = self.ctx.cfg
                providers = dict(cfg.get("providers") or {})
                cur = dict(providers.get("lionbox-custom") or {})
                updates: dict[str, Any] = {"providerMode": "custom"}
                for k in ("baseUrl", "apiKey", "model"):
                    v = ai.get(k)
                    if v is not None and str(v).strip() and not str(v).endswith("••••") and "•" not in str(v):
                        cur[k] = str(v)
                        updates[k] = str(v)
                providers["lionbox-custom"] = cur
                updates["providers"] = providers
                cfg.update(updates)
                target = self.ctx.adapters().get_active_adapter()
                if target is not None:
                    patch = {k: cur[k] for k in ("baseUrl", "apiKey", "model") if cur.get(k)}
                    target.update_config(patch)
                ai_used = {"baseUrl": cur.get("baseUrl", ""), "model": cur.get("model", ""),
                           "hasKey": bool(cur.get("apiKey"))}
            except Exception as e:                           # noqa: BLE001 不让创建被它挡住
                self.log(pid, f"⚠ AI API 应用失败（仍用当前配置继续）: {type(e).__name__}: {e}")
        # 工作区 + 会话（与聊天同一套存储 ⇒ 后续可以在平台里继续聊）
        # 【必须排在扣费之前】这段会因环境问题抛（实测：无 --config-dir 时
        # register_workspace 写 app-config 撞 PermissionError）—— 放扣费之后就是
        # **收钱不交付** ✗✗✗（tenant_e2e 抓到：20分扣了、项目没建成）。先建好，后收钱。
        try:
            deps = self._deps()
            ws_item = deps.workspaces(self.ctx).register_workspace(str(src))
            # 【register_workspace 返回条目 dict {'id','path','permission'}，不是 id】
            # 第一版把整个 dict `str(wid)` 当 workspace_id 传给 create_session ✗✗✗：
            # 会话绑的工作区 id 变成 "{'id': ...}" 垃圾串 ⇒ Agent 写文件时按它拼路径 ⇒
            # WinError 123（非法路径）⇒ 审核放行一直失败 ⇒ Agent 无限重试、files=0、
            # 卡 building 十几分钟（2026-10-17 实测）。取 id 字段（str 也兼容）。
            wid = str(ws_item.get("id") if isinstance(ws_item, dict)
                      else getattr(ws_item, "id", ws_item))
            session = deps.sessions(self.ctx).create_session(wid, "STANDARD")
        except Exception as e:                               # noqa: BLE001 未收钱，干净失败
            shutil.rmtree(src, ignore_errors=True)
            self.pool.release(pid)
            return {"ok": False,
                    "error": f"初始化工作区/会话失败（尚未扣费）: {type(e).__name__}: {e}"}
        # 【会话必须真落盘】SessionManager.createSession 自己不落盘（main 的 POST 里是
        # 显式 _persist_session）—— 平台原来只做了"可写性预检"没真存 ✗✗✗：后端一重启
        # 会话查无，聊天守卫就报"会话已随后端重启丢失"（用户实测撞上 ✗✗✗✗✗）。
        # 真实现持有 .persistence.save_session(Session)；窄桩没有 → 警告不挡
        # （聊天时会按工作区自动重建，见 chat）。
        _sp = deps.sessions(self.ctx)
        _saver = getattr(getattr(_sp, "persistence", None), "save_session", None)
        if callable(_saver) and session is not None and hasattr(session, "session_id"):
            try:
                if not _saver(session):
                    print(f"[平台] ⚠ 会话元数据落盘被拒（重启会丢，聊天时自动重建）: {pid}",
                          flush=True)
            except Exception as e:                           # noqa: BLE001
                print(f"[平台] ⚠ 会话元数据落盘失败（重启会丢，聊天时自动重建）: "
                      f"{type(e).__name__}: {e}", flush=True)
        # 【真实 SessionManager 返回 Session 对象，窄桩返回 dict】两种都认：
        # 对象看 .session_id（team/subagent_tool 同款用法），dict 看 sessionId/id。
        sid_attr = getattr(session, "session_id", None)
        if sid_attr:
            session_id = str(sid_attr)
        elif isinstance(session, dict):
            session_id = str(session.get("sessionId") or session.get("id") or "")
        else:
            session_id = ""
        if not session_id:
            shutil.rmtree(src, ignore_errors=True)
            self.pool.release(pid)
            return {"ok": False, "error": "会话创建失败（拿不到 sessionId）"}

        # ===== 支付 + 独立 IP（购买）—— 排在所有初始化**之后**：收钱必须紧跟交付物 =====
        # 鉴权启用才扣款（开放模式=运维自用，不要钱）；首期=算力(月租/包年)+分项(IP/硬盘)
        # +未结流量；池已配置则分不到 IP 就拒绝购买并全额退款，池未配置则不分配也不计费。
        will_ip = bool(self.ips.pool)
        price = period_total_cents(spec, cpu, mem, disk, will_ip, cycle)
        owner = ""
        paid_until = 0.0
        ip_val: str | None = None
        if self.auth.enabled:
            if not user:
                shutil.rmtree(src, ignore_errors=True)
                self.pool.release(pid)
                return {"ok": False, "error": "未登录"}
            if not self.auth.charge(user, price):
                shutil.rmtree(src, ignore_errors=True)
                self.pool.release(pid)
                return {"ok": False,
                        "error": f"余额不足：首期应付 ¥{price / 100:.2f}"
                                 f"（{'包年 8 折' if cycle == 'year' else '月租'}"
                                 f"{'，含独立 IP 与硬盘' if will_ip else ''}），"
                                 f"当前余额 ¥{self.auth.balance(user) / 100:.2f} —— 找管理员充值"}
            owner = user
            paid_until = time.time() + CYCLE_SECONDS[cycle]
        if self.ips.pool:
            ip_val = self._take_ip()          # 上锁认领（租约防并发拿同一个 IP）
            if ip_val is None:
                if owner:
                    self.auth.credit(owner, price)
                    self.billing.add("refund", owner, "", spec, price, "IP 池占满，购买回滚")
                shutil.rmtree(src, ignore_errors=True)
                self.pool.release(pid)
                return {"ok": False,
                        "error": "独立 IP 池已占满 —— 每台服务器必须带独立 IP，"
                                 "先在管理端归还/扩充 IP 池"}
        if owner:
            days = CYCLE_SECONDS[cycle] / 86400
            self.billing.add("create", owner, pid, spec, price,
                             f"首期预付（{'包年' if cycle == 'year' else '月租'}，"
                             f"{days:g} 天，{'含 IP+硬盘' if will_ip else '无 IP'}）")
            if ip_val:
                self.billing.add("system", owner, pid, spec, 0, f"分配独立 IP {ip_val}")

        item = {"id": pid, "name": name, "prompt": prompt, "cpu": cpu, "memoryMb": mem,
                "spec": spec, "bandwidthMb": bw, "cycle": cycle,
                "egressBytes": 0, "egressBilledBytes": 0,
                "owner": owner, "paidUntil": paid_until, "ip": ip_val,
                "diskGb": disk, "sessionId": session_id, "workspaceId": wid, "aiApi": ai_used,
                "status": ST_CREATED, "kind": "", "createdAt": _now(), "webUrl": None,
                "dlUrl": None, "test": {}, "artifacts": [], "buildReply": "", "error": ""}
        try:
            self.store.add(item)
            self._lease_owned(ip_val)         # 记录接管占用判定，租约退场
        except OSError as e:
            # 落盘失败 = 收钱不交付 ⇒ 必须原路退款（不许吞钱 ✗✗✗）
            self._lease_owned(ip_val)
            if owner:
                self.auth.credit(owner, price)
                self.billing.add("refund", owner, pid, spec, price, "实例落盘失败，退款")
            shutil.rmtree(src, ignore_errors=True)
            self.pool.release(pid)
            return {"ok": False, "error": f"实例保存失败（已退款）: {type(e).__name__}: {e}"}
        self.log(pid, f"实例已创建：{name}（规格 {spec} / 带宽 {bw}M / 磁盘 {disk} GB）"
                      + (f" · 独立 IP {ip_val}" if ip_val
                         else (" · IP 池未配置（管理端添加后新购实例才会分到）"
                               if not self.ips.pool else ""))
                      + (" · " + (f"支付首期 ¥{price / 100:.2f}"
                                  f"（{'包年365天' if cycle == 'year' else '月租30天'}）"
                                  if owner else "开放模式不计费"))
                      + " —— 工作区就绪，Agent 接管构建")
        with LOCK:
            self._busy.add(pid)
        # 供给先行（vm=真虚拟机装 Windows；host=直接构建）—— 支付后的交付衔接
        threading.Thread(target=self._provision_then_build, args=(pid,), daemon=True,
                         name=f"lionforge-build-{pid[:8]}").start()
        return {"ok": True, "id": pid, "sessionId": session_id}

    def chat(self, pid: str, message: str, by: str | None = None) -> dict[str, Any]:
        p = self.store.get(pid)
        if p is None:
            return {"ok": False, "error": "项目不存在"}
        # 【会话丢了 → 按项目工作区自动重建】工作区路径就在项目记录里（workspaceId
        # 就是目录路径，兜底直接用项目目录）—— 重建会话继续聊：历史丢、目录不变、
        # 绝不去错目录。原实现只报错让用户重建项目 ✗✗✗（实测报障：后端重启后旧会话
        # 查无 —— 因为平台此前从没落盘过会话）。
        try:
            alive = self._deps().sessions(self.ctx).get_session(p["sessionId"])
        except Exception:                                   # noqa: BLE001
            alive = None
        if not alive:
            deps = self._deps()
            ws = str(p.get("workspaceId") or "") or str(self.projects_dir / pid)
            try:
                new_sess = deps.sessions(self.ctx).create_session(ws, "STANDARD")
            except Exception as e:                           # noqa: BLE001
                return {"ok": False, "error": f"会话丢失且重建失败: {type(e).__name__}: {e}"}
            sid = str(getattr(new_sess, "session_id", None)
                      or (new_sess.get("sessionId") if isinstance(new_sess, dict) else "") or "")
            if not sid:
                return {"ok": False, "error": "会话丢失且重建失败（拿不到 sessionId）"}
            try:
                _sav = getattr(getattr(deps.sessions(self.ctx), "persistence", None),
                               "save_session", None)
                if callable(_sav) and hasattr(new_sess, "session_id"):
                    _sav(new_sess)
            except Exception as e:                           # noqa: BLE001
                self.log(pid, f"⚠ 重建会话落盘失败: {type(e).__name__}: {e}")
            self.store.update(pid, sessionId=sid)
            self.log(pid, "会话已随后端重启丢失 → 已按工作区自动重建"
                          "（历史丢失，目录不变）: " + sid)
            p["sessionId"] = sid
        # 【限流】熔断器开着 → 友好拒绝（不再把用户的话撞向429云端）
        if self._breaker.tripped():
            return {"ok": False, "error": self._breaker.msg()}
        # 【限流】同用户两轮对话至少隔 3 秒（防连点；busy 已挡同项目并发）
        _who = by or ""
        _now = time.time()
        if _now - float(self._last_chat_at.get(_who, 0.0)) < 3.0:
            return {"ok": False, "error": "限流：两次对话至少隔 3 秒（防连点），稍后再发"}
        self._last_chat_at[_who] = _now
        with LOCK:
            if pid in self._busy:
                return {"ok": False, "error": "项目正在构建/部署中，等它交付后再聊（看状态）"}
            self._busy.add(pid)
        try:
            # 【每条消息都带绝对项目路径】就算 workspace 解析回退，AI 也照绝对路径干活
            src = str(self.projects_dir / pid)
            message = (f"（项目绝对路径：{src} —— 本项目所有文件的读写都必须用这个绝对路径，"
                       f"不要写到别处）\n" + message)
            self.log(pid, f"用户消息: {message[:120]}")
            t0 = time.time()
            reply = self._agent_run(pid, p["sessionId"], message)
            self.log(pid, f"AI 回复（{int(time.time() - t0)}s）: {reply[:200]}")
            # 对话永久存档（chat.jsonl 永远写 + MySQL lion_messages 双写）
            self._archive_chat(pid, str(p["sessionId"]),
                               by or str(p.get("owner") or ""), message, reply)
            # 【熔断】成功闭合、失败开闸 —— 只认"真的发生了模型往返"的回复：
            # 失败文案以"模型调用失败"开头；工具/依赖异常、重建失败等前缀说明模型
            # 根本没被调用，**既不开闸也不许闭合**（否则配额还没恢复就被误放行 ✗✗✗）
            if "模型调用失败" in reply:
                self._breaker.fail()
            elif not reply.startswith(("工具/依赖异常", "会话丢失且重建失败", "平台会话不可用")):
                self._breaker.ok()
            # 改动后服务若在跑，重启一次让它带新代码（最朴素但可靠的部署语义）
            note = ""
            if pid in self._procs:
                note = "已重启部署服务（改动已生效）"
                self._restart_deploy(pid)
            return {"ok": True, "reply": reply, "note": note}
        except Exception as e:                               # noqa: BLE001
            self.log(pid, f"聊天异常: {type(e).__name__}: {e}")
            return {"ok": False, "error": f"{type(e).__name__}: {e}"}
        finally:
            with LOCK:
                self._busy.discard(pid)

    def _restart_deploy(self, pid: str) -> None:
        p = self.store.get(pid)
        src = self.projects_dir / pid
        self._stop_proc(pid)                # 统一走停进程助手（否则旧进程会成孤儿）
        port = int(p.get("port") or 0)
        if not port or not self._port_free(port):
            port = self._pick_port()
        if not port:
            self.log(pid, "⚠ 无可用端口，部署未重启")
            return
        proc = self._start_server(pid, src, port)
        if proc is not None:
            self._procs[pid] = proc
            ok, code, _ = self._probe(port)
            self.store.update(pid, port=port, webUrl=f"/serve/{pid}/",
                              test=dict(p.get("test") or {}, ok=ok, http=code))
            self.log(pid, f"部署已重启: ok={ok} http={code}")

    def stop_project(self, pid: str) -> dict[str, Any]:
        p = self.store.get(pid)
        if p is None:
            return {"ok": False, "error": "项目不存在"}
        # 先改状态再杀进程：构建线程的后续写入都会被 `_still_running` 挡掉
        # （否则 stop 后构建线程照样把状态改回 live 并起服务 ✗✗✗）
        # ip=None：停止 = 实例下线，独立 IP 立即归还池（与配额同进退）
        self._flush_egress(pid)                      # 停止前把未结流量落账
        self.store.update(pid, status=ST_STOPPED, ip=None)
        self._stop_proc(pid)
        self.pool.release(pid)
        self.log(pid, "已停止（服务进程已终止；配额与独立 IP 均已归还池）")
        return {"ok": True}

    def delete_project(self, pid: str) -> dict[str, Any]:
        """删除实例：停进程 → 释放配额 → 删记录（IP 随记录归还）→ 回收磁盘目录。

        【为什么必须有这个接口】没有删除手段时，失败/停止的项目目录**无限堆积**
        = 磁盘耗尽攻击面（攻击者视角 ✗✗✗）；而磁盘配额只是"登记+核对"，并没有
        运行时硬限（硬限要 FSUTIL/受限账户，见 README 已知限制）—— 至少要给运维
        一个回收杠杆。账单流水保留（删除本身记一条 0 分 system 行）。
        """
        p = self.store.get(pid)
        if p is None:
            return {"ok": False, "error": "项目不存在"}
        with LOCK:
            if pid in self._busy:
                return {"ok": False, "error": "正在构建/部署中 —— 先停止再删除"}
        self._stop_proc(pid)                    # 防残留服务进程继续占端口
        self._flush_egress(pid)
        self.pool.release(pid)
        self._lease_owned(str(p.get("ip") or "") or None)
        if not self.store.remove(pid):         # IP 随记录消失 = 归还池
            return {"ok": False, "error": "项目不存在"}
        shutil.rmtree(self.projects_dir / pid, ignore_errors=True)
        owner = str(p.get("owner") or "")
        if owner and self.auth.enabled:
            self.billing.add("system", owner, pid, str(p.get("spec") or ""), 0,
                             "实例已删除（磁盘/配额/IP 已回收）")
        print(f"[平台] 实例已删除: {pid}", flush=True)
        return {"ok": True}


# ============================================================ HTTP 出口
MIME = {".html": "text/html; charset=utf-8", ".js": "application/javascript; charset=utf-8",
        ".css": "text/css; charset=utf-8", ".json": "application/json; charset=utf-8",
        ".png": "image/png", ".svg": "image/svg+xml", ".jpg": "image/jpeg",
        ".ico": "image/x-icon", ".txt": "text/plain; charset=utf-8", ".zip": "application/zip",
        ".md": "text/plain; charset=utf-8"}


def _pid_of(req_path: str, tail: str) -> str:
    """从 /api/platform/projects/<pid>/<tail> 里取出 pid。
    【踩过的坑】第一版写 `path.split("/")[-1]` ⇒ 对 /chat、/log、/stop 取到的是
    "chat"/"log"/"stop" 本身 ✗✗✗（详情接口没有尾巴所以没暴露）⇒ 聊天永远 409"项目不存在"。
    """
    m = re.search(r"^/api/platform/projects/([^/]+)" + re.escape(tail) + r"/?$", req_path)
    return m.group(1) if m else ""


def register(router: Any, ctx: Any, Response: Any, gates: list[Any] | None = None) -> None:
    """把 TigerForge 挂到后端路由上（main 的 register__api_platform 调用）。

    gates：main 传进来的 `_HTTP_GATES` —— 进门门（①按独立 IP 直达实例应用
    ②登录鉴权）注册进去，由 `_serve` 在租户锁定与路由匹配之前执行。
    """
    api = PlatformApi(ctx, Response)
    if gates is not None:
        gates.append(api.http_gate)

    # 计费心跳：每小时给 live 项目扣时费（鉴权启用才动钱；余额不够 → 停机不欠账）
    def _billing_loop() -> None:
        while True:
            time.sleep(3600)
            try:
                r = api._tick_billing()
                if r.get("charged") or r.get("stopped"):
                    print(f"[平台] 计费心跳: 扣费 {len(r['charged'])} 台 / "
                          f"停机 {len(r['stopped'])} 台", flush=True)
            except Exception as e:                           # noqa: BLE001
                print(f"[平台] 计费心跳异常: {type(e).__name__}: {e}", flush=True)

    threading.Thread(target=_billing_loop, daemon=True, name="lionforge-billing").start()

    @router.get("/platform")
    def platform_page(req: Any) -> Any:
        # no-cache：页面里的 JS/表单经常更新，浏览器缓存住旧版会让"下拉没选项"
        # 这类问题怎么刷新都好不了（只改服务端不改缓存策略 = 白修 ✗✗✗）。
        return Response(PLATFORM_HTML, content_type="text/html; charset=utf-8",
                        headers={"Cache-Control": "no-cache, must-revalidate"})

    @router.get("/admin")
    def platform_admin_page(req: Any) -> Any:
        """管理后台（用户要求: 用户界面和后台分开）。
        同一份 HTML，JS 按 pathname 渲染后台视图；**用户面 /platform 里没有任何管理
        控件**；角色门把非管理员的 /admin 直接 403（连 HTML 都拿不到）。"""
        return Response(PLATFORM_HTML, content_type="text/html; charset=utf-8",
                        headers={"Cache-Control": "no-cache, must-revalidate"})

    @router.get("/api/platform/info")
    def platform_info(req: Any) -> Any:
        return Response.json(api.info())

    # ---- 账号（登录/注册/登出） ----
    @router.get("/api/auth/me")
    def auth_me(req: Any) -> Any:
        if not api.auth.enabled:
            return api._json({"authEnabled": False})
        u = api.user_of(req)
        if not u:
            return api._json({"authEnabled": True, "error": "未登录"}, 401)
        return api._json({"authEnabled": True, "username": u,
                          "balance": api.auth.balance(u),
                          "admin": api.auth.is_admin(u)})

    @router.post("/api/auth/register")
    def auth_register(req: Any) -> Any:
        body = req.json_obj() if hasattr(req, "json_obj") else {}
        body = body if isinstance(body, dict) else {}
        # 未启用 = 建首个账号（部署者本人，天然管理员）；已启用 = 只有管理员能开号
        if api.auth.enabled and not api.auth.is_admin(api.user_of(req)):
            return api._json({"success": False, "error": "只有管理员能创建账号"}, 403)
        name = str(body.get("username") or "")
        err = api.auth.create_user(name, str(body.get("password") or ""))
        if err:
            return api._json({"success": False, "error": err}, 400)
        api.billing.add("system", name.strip(), "", "", 0,
                        "账号创建（管理员）" if api.auth.is_admin(name.strip()) else "账号创建")
        if len(api.auth.users) == 1:
            # 首个账号=管理员 —— 公网暴露期间建号 = 抢管理员的竞速窗口（README 已注明
            # "先建号再开放"）；来源 IP 必须留痕，出事查得到人。
            print(f"[平台] 首个管理员账号 '{name.strip()}' 由 "
                  f"{getattr(req, 'client', '?')} 创建", flush=True)
        return api._json({"success": True, "admin": api.auth.is_admin(name.strip())})

    @router.post("/api/auth/login")
    def auth_login(req: Any) -> Any:
        body = req.json_obj() if hasattr(req, "json_obj") else {}
        body = body if isinstance(body, dict) else {}
        token = api.auth.login(str(body.get("username") or ""),
                               str(body.get("password") or ""),
                               client=str(getattr(req, "client", "") or ""))
        if token == AuthStore.LOCKED:
            left = api.auth.lock_left(str(body.get("username") or ""),
                                      str(getattr(req, "client", "") or ""))
            return api._json({"success": False,
                              "error": f"失败次数过多，已锁定 —— {left} 秒后可重试"
                                       f"（锁定期内**正确密码也进不去**；锁定为内存态，"
                                       f"后端重启即清）"}, 429)
        if not token:
            # 不区分"用户不存在 / 密码错"（不给枚举账号的口子）
            return api._json({"success": False, "error": "用户名或密码不对"}, 401)
        return api._json({"success": True}, headers={
            "Set-Cookie": f"lion_sid={token}; Path=/; HttpOnly; SameSite=Lax; "
                          f"Max-Age={AuthStore.TTL}"})

    @router.post("/api/auth/logout")
    def auth_logout(req: Any) -> Any:
        t = api._cookie_token(req)
        if t:
            api.auth.logout(t)
        return api._json({"success": True},
                         headers={"Set-Cookie": "lion_sid=; Path=/; HttpOnly; Max-Age=0"})

    # ---- 账单 ----
    @router.get("/api/platform/billing")
    def billing_list(req: Any) -> Any:
        pricing = {"month": BASE_MONTH_CENTS, "year": BASE_YEAR_CENTS,
                   "ipMonth": IP_MONTH_CENTS, "diskGbMonth": DISK_GB_MONTH_CENTS,
                   "trafficGb": TRAFFIC_GB_CENTS}
        if not api.auth.enabled:
            return api._json({"enabled": False, "rows": [], "pricing": pricing})
        me = api.user_of(req)
        all_rows = req.q("all") == "1" and api.auth.is_admin(me)
        return api._json({"enabled": True, "pricing": pricing,
                          "balance": api.auth.balance(me),
                          "rows": api.billing.list(user=None if all_rows else me)})

    # ---- 管理端（全部要求管理员） ----
    @router.post("/api/platform/admin/topup")
    def admin_topup(req: Any) -> Any:
        denied = api._require_admin(req)
        if denied is not None:
            return denied
        body = req.json_obj() if hasattr(req, "json_obj") else {}
        body = body if isinstance(body, dict) else {}
        target = str(body.get("username") or "").strip()
        if target not in api.auth.users:
            return api._json({"success": False, "error": f"用户不存在: {target}"}, 404)
        try:
            cents = (int(body["cents"]) if body.get("cents") is not None
                     else int(round(float(body.get("yuan") or 0) * 100)))
        except (TypeError, ValueError):
            return api._json({"success": False, "error": "金额必须是数字"}, 400)
        if cents <= 0:
            return api._json({"success": False, "error": "充值金额必须为正（元或分）"}, 400)
        api.auth.credit(target, cents)
        api.billing.add("topup", target, "", "", cents,
                        "管理端充值（占位：真实支付需接支付网关）")
        return api._json({"success": True, "balance": api.auth.balance(target)})

    @router.get("/api/platform/admin/ips")
    def admin_ips_get(req: Any) -> Any:
        denied = api._require_admin(req)
        if denied is not None:
            return denied
        taken = {str(p.get("ip")): p["id"] for p in api.store.all() if p.get("ip")}
        rows = [{"ip": ip, "onMachine": ip_on_this_machine(ip),
                 "projectId": taken.get(ip), "used": ip in taken} for ip in api.ips.pool]
        return api._json({
            "pool": rows,
            "hint": "真实 IP 先用管理员权限绑到网卡再入池："
                    'netsh interface ipv4 add address "网卡名" <IP> <子网掩码>'})

    @router.post("/api/platform/admin/ips")
    def admin_ips_add(req: Any) -> Any:
        denied = api._require_admin(req)
        if denied is not None:
            return denied
        body = req.json_obj() if hasattr(req, "json_obj") else {}
        err = api.ips.add(str((body or {}).get("ip") or ""))
        if err:
            return api._json({"success": False, "error": err}, 400)
        return api._json({"success": True, "pool": api.ips.pool})

    @router.post("/api/platform/admin/ips/remove")
    def admin_ips_del(req: Any) -> Any:
        denied = api._require_admin(req)
        if denied is not None:
            return denied
        body = req.json_obj() if hasattr(req, "json_obj") else {}
        ok = api.ips.remove(str((body or {}).get("ip") or ""))
        return api._json({"success": ok, "pool": api.ips.pool},
                         status=200 if ok else 404)

    @router.post("/api/platform/billing/tick")
    def billing_tick(req: Any) -> Any:
        """管理端补扣/演练心跳：带 periods= 补扣 N 期（1..12）；余额不够的实例停机不欠账。"""
        denied = api._require_admin(req)
        if denied is not None:
            return denied
        body = req.json_obj() if hasattr(req, "json_obj") else {}
        periods = (body or {}).get("periods")
        out = api._tick_billing(
            force_periods=float(periods) if periods is not None else None)
        if out.get("error"):
            return api._json(out, 400)
        return api._json(out)

    @router.get("/api/platform/admin/users")
    def admin_users(req: Any) -> Any:
        """后台·全部用户（用户名/角色/余额/注册时间 —— 不含盐与哈希）。"""
        denied = api._require_admin(req)
        if denied is not None:
            return denied
        rows = [{"username": k, "admin": bool(v.get("admin")),
                 "balance": int(v.get("balance") or 0), "created": v.get("created")}
                for k, v in api.auth.users.items()]
        rows.sort(key=lambda x: str(x.get("created") or ""))
        return api._json({"users": rows, "authEnabled": api.auth.enabled})

    @router.get("/api/platform/admin/projects")
    def admin_projects(req: Any) -> Any:
        """后台·全部项目实例（跨用户总览）。"""
        denied = api._require_admin(req)
        if denied is not None:
            return denied
        rows = [{"id": p.get("id"), "name": p.get("name"), "owner": p.get("owner"),
                 "status": p.get("status"), "spec": p.get("spec"), "ip": p.get("ip"),
                 "createdAt": p.get("createdAt"), "paidUntil": p.get("paidUntil")}
                for p in sorted(api.store.all(), key=lambda x: x.get("createdAt", ""),
                                reverse=True)]
        return api._json({"rows": rows})

    @router.get("/api/platform/projects")
    def platform_list(req: Any) -> Any:
        items = sorted(api.store.all(), key=lambda x: x.get("createdAt", ""), reverse=True)
        # 【按用户隔离】鉴权启用时：管理员看全部，普通用户只看自己的（老项目没有
        # owner ⇒ 只有管理员能看见，不自动落进任何租户名下）。
        if api.auth.enabled:
            me = api.user_of(req)
            if not api.auth.is_admin(me):
                items = [p for p in items if (p.get("owner") or "") == (me or "")]
        return Response.json({"items": items, "busy": sorted(api._busy)})

    @router.post("/api/platform/projects")
    def platform_create(req: Any) -> Any:
        body = req.json_obj() if hasattr(req, "json_obj") else {}
        if not isinstance(body, dict):
            body = {}
        out = api.create_project(body, api.user_of(req))
        return Response.json(out, status=200 if out.get("ok") else 400)

    @router.get("/api/platform/projects/{pid}")
    def platform_detail(req: Any) -> Any:
        pid = req.path.rstrip("/").split("/")[-1]
        p = api.store.get(pid)
        if p is None or not api._owner_ok(req, p):
            # 非 owner 一律按"不存在"回（不泄露"存在但不是你的"）
            return Response.json({"ok": False, "error": "项目不存在"}, status=404)
        p["log"] = api.read_log(pid)
        p["busy"] = pid in api._busy
        api._flush_egress(pid)                  # 详情页展示流量前先落账
        p = api.store.get(pid) or p
        if p.get("ip"):
            # bind 试一次即知该 IP 在不在本机网卡上（详情页据此显示"✓直达/⚠需netsh"）
            p["ipInfo"] = {"ip": p["ip"], "onMachine": ip_on_this_machine(str(p["ip"]))}
        # 密钥不回显（平台页只显示 hasKey）
        p["aiApi"] = {"baseUrl": (p.get("aiApi") or {}).get("baseUrl", ""),
                      "model": (p.get("aiApi") or {}).get("model", ""),
                      "hasKey": bool((p.get("aiApi") or {}).get("hasKey"))}
        return Response.json(p)

    @router.get("/api/platform/projects/{pid}/log")
    def platform_log(req: Any) -> Any:
        pid = _pid_of(req.path, "/log")
        if not api._owner_ok(req, api.store.get(pid)):
            return Response.json({"ok": False, "error": "项目不存在"}, status=404)
        return Response(api.read_log(pid, tail=200), content_type="text/plain; charset=utf-8")

    @router.post("/api/platform/projects/{pid}/chat")
    def platform_chat(req: Any) -> Any:
        pid = _pid_of(req.path, "/chat")
        if not api._owner_ok(req, api.store.get(pid)):
            return Response.json({"ok": False, "error": "项目不存在"}, status=404)
        body = req.json_obj() if hasattr(req, "json_obj") else {}
        msg = str((body or {}).get("message") or "").strip()
        if not msg:
            return Response.json({"ok": False, "error": "消息为空"}, status=400)
        out = api.chat(pid, msg, api.user_of(req))
        return Response.json(out, status=200 if out.get("ok") else 409)

    @router.get("/api/platform/projects/{pid}/messages")
    def platform_messages(req: Any) -> Any:
        """对话历史（永久存储的读取面；owner 校验）。来源: chat.jsonl（永远有）；
        MySQL 模式下同一份对话在 lion_messages 表里另有一份（双写）。"""
        pid = _pid_of(req.path, "/messages")
        if not api._owner_ok(req, api.store.get(pid)):
            return Response.json({"ok": False, "error": "项目不存在"}, status=404)
        rows: list[dict[str, Any]] = []
        f = api.projects_dir / pid / ".lionforge" / "chat.jsonl"
        try:
            for line in f.read_text(encoding="utf-8", errors="replace").splitlines()[-200:]:
                line = line.strip()
                if not line:
                    continue
                try:
                    rows.append(json.loads(line))
                except json.JSONDecodeError:
                    continue            # 半行容错（写入中断的尾巴不害读）
        except OSError:
            pass
        return api._json({"rows": rows, "db": api.auth.account_db,
                          "note": "MySQL 模式下同一份对话另存 lion_messages 表（双写）"})

    @router.post("/api/platform/projects/{pid}/stop")
    def platform_stop(req: Any) -> Any:
        pid = _pid_of(req.path, "/stop")
        if not api._owner_ok(req, api.store.get(pid)):
            return Response.json({"ok": False, "error": "项目不存在"}, status=404)
        return Response.json(api.stop_project(pid))

    @router.post("/api/platform/projects/{pid}/delete")
    def platform_delete(req: Any) -> Any:
        """删除实例（owner/管理员）。构建中先停止 —— busy 在 delete_project 里挡。"""
        pid = _pid_of(req.path, "/delete")
        if not api._owner_ok(req, api.store.get(pid)):
            return Response.json({"ok": False, "error": "项目不存在"}, status=404)
        out = api.delete_project(pid)
        return Response.json(out, status=200 if out.get("ok") else 409)

    @router.post("/api/platform/projects/{pid}/redeploy")
    def platform_redeploy(req: Any) -> Any:
        """重新自测 + 部署（后端重启后 _procs 丢了、或用户手改了代码时用）。"""
        pid = _pid_of(req.path, "/redeploy")
        p = api.store.get(pid)
        if p is None or not api._owner_ok(req, p):
            return Response.json({"ok": False, "error": "项目不存在"}, status=404)
        with LOCK:
            if pid in api._busy:
                return Response.json({"ok": False, "error": "项目正在忙"}, status=409)
            api._busy.add(pid)

        def run() -> None:
            try:
                # 【先停旧、再确保配额】原实现直接 _start_server ⇒ 旧进程成孤儿、
                # 新进程绑不上端口（端口被旧进程占着）✗✗✗；配额若因失败/重启不在册，
                # 也要在这里重新划走，否则等于绕过物理机总池。
                api._stop_proc(pid)
                qerr = api._ensure_quota(pid)
                if qerr:
                    api.log(pid, f"重新部署被拒：{qerr}")
                    api.store.update(pid, status=ST_FAILED, error=qerr)
                    return
                api.log(pid, "重新部署（自测 + 部署）…")
                api._test_and_deploy(pid, api.projects_dir / pid)
            except Exception as e:                           # noqa: BLE001
                api.log(pid, f"❌ 重新部署异常: {type(e).__name__}: {e}")
                api._release_quota(pid, "重新部署异常")
                if api._still_running(pid):
                    api.store.update(pid, status=ST_FAILED, error=f"{type(e).__name__}: {e}")
            finally:
                with LOCK:
                    api._busy.discard(pid)

        threading.Thread(target=run, daemon=True, name=f"lionforge-redeploy-{pid[:8]}").start()
        return Response.json({"ok": True})

    @router.post("/api/platform/projects/{pid}/rebuild")
    def platform_rebuild(req: Any) -> Any:
        """重新执行初始提示词：整条构建链重跑（构建→自测→部署）。
        场景: 构建失败后想一键重试（比如云端429把 Agent 打死在第一轮、零产物），
        不用重建项目、不用会话里复述提示词 —— 提示词就在项目记录里。"""
        pid = _pid_of(req.path, "/rebuild")
        p = api.store.get(pid)
        if p is None or not api._owner_ok(req, p):
            return Response.json({"ok": False, "error": "项目不存在"}, status=404)
        # 省钱闸（熔断器）：云端刚 429 → 拒绝重建（免得又是14秒死的空转）
        if api._breaker.tripped():
            return Response.json({"ok": False, "error": api._breaker.msg()}, status=409)
        with LOCK:
            if pid in api._busy:
                return Response.json({"ok": False, "error": "项目正在忙"}, status=409)
            api._busy.add(pid)
        api.log(pid, "重新构建（重跑初始提示词整条链）…")
        threading.Thread(target=api._build_pipeline, args=(pid,), daemon=True,
                         name=f"lionforge-rebuild-{pid[:8]}").start()
        return Response.json({"ok": True})

    # {rest*} = 多段透传（Router 支持 `{name*}` 匹配剩余全部段）——部署应用的
    # HTML 里都是相对路径（./app.js、/assets/x.css），必须整段转给它。
    # 【尾斜杠必须单独注册】`{rest*}` 用 `.+`（非空），`/serve/<id>/` 的 rest 是空串 ⇒
    # 两个模板都罩不住它（实测 404"没有这个接口" ✗✗✗），所以把 "/" 版本显式加上。
    @router.get("/serve/{pid}")
    @router.get("/serve/{pid}/")
    @router.get("/serve/{pid}/{rest*}")
    @router.post("/serve/{pid}")
    @router.post("/serve/{pid}/")
    @router.post("/serve/{pid}/{rest*}")
    def serve_deployed(req: Any) -> Any:
        parts = req.path.split("/")
        pid = parts[2]
        rest = "/".join(parts[3:]) if len(parts) > 3 else ""
        # 分发唯一实现在 dispatch_deployed —— /serve 与"按独立 IP 直达"共用一份
        return api.dispatch_deployed(pid, rest)

    @router.get("/dl/{pid}")
    @router.get("/dl/{pid}/")
    def download_page(req: Any) -> Any:
        pid = req.path.rstrip("/").split("/")[-1]
        p = api.store.get(pid)
        if p is None:
            return Response.json({"ok": False, "error": "项目不存在"}, status=404)
        return Response(_dl_html(api, p), content_type="text/html; charset=utf-8")

    @router.get("/dl/{pid}/{name}")
    def download_file(req: Any) -> Any:
        parts = req.path.split("/")
        pid, name = parts[2], parts[3]
        if api.store.get(pid) is None:
            return Response.json({"ok": False, "error": "项目不存在"}, status=404)
        # 【防穿越】name 是 URL 段（不含 /）但**含反斜杠合法** —— Windows 把 `\` 也当
        # 分隔符，`..%5C..%5C别的项目\...` 能跨出 .lionforge 读到别的租户文件（推演 ✗✗✗）。
        # 三道防线：字符拒收 → resolve 后必须仍在 .lionforge 内 → 才允许读。
        if (not name or name in (".", "..") or ".." in name or "\\" in name
                or any(ch in name for ch in '<>:"|?*')):
            return Response.json({"ok": False, "error": "非法文件名"}, status=400)
        base = (api.projects_dir / pid / ".lionforge").resolve()
        f = (base / name).resolve()
        try:
            f.relative_to(base)
        except ValueError:
            return Response.json({"ok": False, "error": "非法路径"}, status=400)
        if not f.is_file():
            return Response.json({"ok": False, "error": "产物不存在"}, status=404)
        ctype = MIME.get(f.suffix.lower(), "application/octet-stream")
        safe = name.replace('"', "").replace("\r", "").replace("\n", "")
        data = f.read_bytes()
        api._add_egress(pid, len(data))          # 下载也是出站（0.5元/GB 计费口径）
        return Response(data, content_type=ctype,
                        headers={"Content-Disposition": f'attachment; filename="{safe}"'})


def _dl_html(api: PlatformApi, p: dict[str, Any]) -> str:
    # 【项目名/文件名是外部输入】f-string 直接进 HTML = XSS；下载页与平台页同一
    # origin，恶意租户起个 <script> 名字就能在别人打开下载页时执行（多租户服务器是真风险）。
    from html import escape as _esc
    pname = _esc(str(p.get("name") or ""))
    rows = []
    for name in p.get("artifacts") or []:
        f = api.projects_dir / p["id"] / ".lionforge" / name
        size = f"{f.stat().st_size // 1024} KB" if f.is_file() else "缺失"
        rows.append(f'<tr><td><a href="/dl/{p["id"]}/{urllib.parse.quote(name)}">'
                    f'{_esc(str(name))}</td><td>{size}</td></tr>')
    body = "\n".join(rows) or '<tr><td colspan="2">（还没有产物）</td></tr>'
    return f"""<!DOCTYPE html><html lang="zh-CN"><head><meta charset="utf-8">
<title>{pname} · 下载</title>
<style>body{{background:#0d1117;color:#e6edf3;font:15px/1.7 -apple-system,"Segoe UI",Consolas,sans-serif;}}
.wrap{{max-width:760px;margin:40px auto;padding:0 20px}}a{{color:#e3b341}}
table{{width:100%;border-collapse:collapse;margin-top:16px}}th,td{{border:1px solid #30363d;padding:8px 12px;text-align:left}}</style>
</head><body><div class="wrap">
<h1>{pname}</h1><p class="muted">由 TigerForge（虎铸）构建与部署 · {_esc(str(p.get('kind', '')))}</p>
<table><tr><th>产物</th><th>大小</th></tr>{body}</table>
<p><a href="/platform">← 返回 TigerForge</a></p></div></body></html>"""


# ============================================================ 平台页（自包含，无外链）
PLATFORM_HTML = r"""<!DOCTYPE html>
<html lang="zh-CN"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>TigerForge 虎铸 · 项目 AI 开发平台</title>
<style>
:root{--bg:#0b0e13;--panel:#141a22;--panel2:#1a212b;--fg:#e8edf4;--mut:#8b96a6;--acc:#ffb638;--acc2:#e39422;--ok:#3fb950;--bad:#f85149;--line:#262e3a;--line2:#313b4a}
*{box-sizing:border-box}
body{margin:0;color:var(--fg);font:14.5px/1.65 -apple-system,"Segoe UI",Consolas,"Microsoft YaHei",sans-serif;
 background:var(--bg);
 background-image:radial-gradient(900px 480px at 18% -10%,rgba(255,182,56,.10),transparent 60%),
 radial-gradient(760px 420px at 110% 8%,rgba(78,140,255,.08),transparent 60%),
 linear-gradient(180deg,rgba(255,255,255,.022),transparent 240px);
 background-attachment:fixed}
.wrap{max-width:1120px;margin:0 auto;padding:0 20px 90px}
h1{font-size:20px;margin:0}
.sub{color:var(--mut);margin-bottom:14px}
.panel{background:linear-gradient(180deg,var(--panel2),var(--panel));border:1px solid var(--line);border-radius:12px;padding:18px 20px;margin-bottom:16px;box-shadow:0 8px 24px rgba(0,0,0,.25)}
label{display:block;color:var(--mut);font-size:12.5px;letter-spacing:.04em;margin:12px 0 5px}
input,select,textarea{width:100%;background:#0d1116;color:var(--fg);border:1px solid var(--line2);border-radius:8px;padding:10px 12px;font:inherit;transition:border-color .15s,box-shadow .15s}
input:focus,select:focus,textarea:focus{outline:0;border-color:var(--acc);box-shadow:0 0 0 3px rgba(255,182,56,.18)}
textarea{min-height:86px;resize:vertical}
.row{display:grid;grid-template-columns:repeat(auto-fit,minmax(160px,1fr));gap:14px}
button{background:linear-gradient(180deg,#ffc553,var(--acc2));color:#241400;border:0;border-radius:8px;padding:10px 18px;font:inherit;font-weight:700;cursor:pointer;letter-spacing:.06em;transition:filter .15s,transform .05s}
button:hover{filter:brightness(1.07)}button:active{transform:translateY(1px)}
button.ghost{background:transparent;color:var(--fg);border:1px solid var(--line2);font-weight:500;padding:8px 14px;margin-right:6px;letter-spacing:0}
button.ghost:hover{border-color:var(--acc);color:var(--acc);filter:none}
button.danger{background:transparent;color:var(--bad);border:1px solid rgba(248,81,73,.5);font-weight:500;padding:8px 14px;letter-spacing:0}
button.danger:hover{background:rgba(248,81,73,.12);filter:none}
button:disabled{opacity:.45;cursor:default;filter:none}
.badge{display:inline-block;padding:2px 10px;border-radius:99px;font-size:12px;border:1px solid var(--line2);letter-spacing:.03em}
.b-building,.b-testing,.b-deploying,.b-provisioning{color:var(--acc);border-color:rgba(255,182,56,.55);background:rgba(255,182,56,.10)}
.b-live{color:#4ade80;border-color:rgba(63,185,80,.55);background:rgba(63,185,80,.10)}
.b-failed{color:var(--bad);border-color:rgba(248,81,73,.5);background:rgba(248,81,73,.09)}
.b-stopped,.b-created{color:var(--mut);background:rgba(139,150,166,.10)}
.card{border:1px solid var(--line);border-radius:10px;padding:14px 16px;margin-bottom:13px;background:linear-gradient(180deg,rgba(26,33,43,.72),rgba(20,26,34,.92));transition:border-color .15s,box-shadow .15s}
.card:hover{border-color:var(--line2);box-shadow:0 6px 18px rgba(0,0,0,.28)}
/* 状态即读: 卡片左侧按状态给色条（扫一眼就知道哪个活着哪个挂了） */
.card:has(.b-live){border-left:3px solid var(--ok)}
.card:has(.b-failed){border-left:3px solid var(--bad)}
.card:has(.b-building),.card:has(.b-provisioning),.card:has(.b-testing),.card:has(.b-deploying){border-left:3px solid var(--acc)}
.card:has(.b-stopped){border-left:3px solid var(--line2)}
.muted{color:var(--mut);font-size:13px}
pre{background:#0a0d12;border:1px solid var(--line);border-radius:8px;padding:10px;max-height:300px;overflow:auto;font-size:12.5px;white-space:pre-wrap}
.err{color:var(--bad)}a{color:var(--acc);text-decoration:none}a:hover{text-decoration:underline}
.grid2{display:grid;grid-template-columns:1fr 1fr;gap:16px}@media(max-width:820px){.grid2{grid-template-columns:1fr}}
.eyebrow{font-size:12px;letter-spacing:.16em;text-transform:uppercase;color:var(--acc);font-weight:700;margin:2px 0 6px}
/* ── 登录 hero ── */
#v-landing{min-height:100vh;display:flex;align-items:center;justify-content:center;padding:24px}
.hero{display:flex;flex-direction:column;align-items:center;gap:26px}
.brand{display:flex;align-items:center;gap:14px}
.logo{width:52px;height:52px;border-radius:14px;flex:0 0 auto;display:flex;align-items:center;justify-content:center;font-size:27px;font-weight:800;color:#241400;
 background:linear-gradient(135deg,#ffd166,var(--acc2));box-shadow:0 6px 22px rgba(255,182,56,.35)}
.bt{font-size:27px;font-weight:800;letter-spacing:.02em;line-height:1.2}
.bt span{color:var(--acc);font-weight:600;font-size:20px;margin-left:6px}
.bs{color:var(--mut);font-size:13.5px;letter-spacing:.06em}
.loginbig{width:min(460px,94vw);background:linear-gradient(180deg,rgba(26,33,43,.96),rgba(20,26,34,.98));border:1px solid var(--line2);border-radius:16px;padding:32px 32px 26px;box-shadow:0 18px 60px rgba(0,0,0,.45);position:relative;overflow:hidden}
.loginbig::before{content:"";position:absolute;inset:0 0 auto 0;height:2px;background:linear-gradient(90deg,transparent,rgba(255,182,56,.75),transparent)}
.loginbig h2{margin:0 0 4px;font-size:21px}
.loginbig .btnrow{display:flex;gap:10px;margin-top:20px}
.loginbig .btnrow button{flex:1;padding:12px 10px}
.err{min-height:1.2em}
.chips{display:flex;flex-wrap:wrap;gap:7px;margin-top:18px;padding-top:16px;border-top:1px dashed var(--line2)}
.chip{font-size:12px;color:#cdd6e3;background:rgba(255,182,56,.10);border:1px solid rgba(255,182,56,.30);border-radius:99px;padding:3px 11px;letter-spacing:.02em}
.chip.free{background:rgba(63,185,80,.10);border-color:rgba(63,185,80,.35)}
/* ── 应用顶栏 ── */
.bar{display:flex;flex-wrap:wrap;gap:10px;align-items:center;justify-content:space-between;padding:16px 0 14px;border-bottom:1px solid var(--line);margin-bottom:18px}
.bar h1 .mini{font-size:14px;color:var(--mut);font-weight:500;margin-left:6px}
#userbar{display:flex;align-items:center;gap:8px;flex-wrap:wrap;justify-content:flex-end}
.uchip{display:inline-flex;align-items:center;gap:8px;background:var(--panel);border:1px solid var(--line2);border-radius:99px;padding:5px 6px 5px 12px;font-size:13px}
.udot{width:22px;height:22px;border-radius:50%;background:linear-gradient(135deg,#4e8cff,#818cf8);display:inline-flex;align-items:center;justify-content:center;font-size:12px;font-weight:700;color:#08101f}
.bal{background:rgba(255,182,56,.14);border:1px solid rgba(255,182,56,.4);color:#ffd166;border-radius:99px;padding:2px 10px;font-weight:700;font-variant-numeric:tabular-nums}
.bigbtn{font-size:15.5px;padding:13px 30px;border-radius:10px;box-shadow:0 6px 18px rgba(255,182,56,.28)}
table.bill{width:100%;border-collapse:collapse;margin-top:8px;font-size:13.5px}
table.bill td,table.bill th{border-bottom:1px solid var(--line);padding:8px 10px;text-align:left}
table.bill tr:nth-child(even) td{background:rgba(255,255,255,.022)}
table.bill td.n{text-align:right;font-variant-numeric:tabular-nums;font-weight:700}
</style></head><body>
<!-- ========== 大登录页（落地页） ========== -->
<div class="wrap" id="v-landing">
 <div class="hero">
  <div class="brand">
   <div class="logo">虎</div>
   <div><div class="bt">TigerForge<span>虎铸</span></div>
        <div class="bs">自带 Agent 的云主机 · 项目 AI 开发平台</div></div>
  </div>
  <div class="loginbig">
   <h2 id="lt">登录 TigerForge</h2>
   <div class="muted" id="lsub">用管理员分配的账号登录</div>
   <label>用户名</label><input id="authuser" autocomplete="username" spellcheck="false">
   <label>密码</label><input id="authpw" type="password" autocomplete="current-password"
     onkeydown="if(event.key==='Enter')authLogin()">
   <div class="btnrow">
     <button onclick="authLogin()">登 录</button>
     <button class="ghost" id="btnreg" onclick="authRegister()" style="display:none">创建首个账号</button>
   </div>
   <div class="err" id="authmsg"></div>
   <div class="muted" id="authhint"></div>
   <div class="chips" id="lprice"></div>
  </div>
 </div>
</div>

<!-- ========== 应用（登录后） ========== -->
<div class="wrap" id="v-app" style="display:none">
  <div class="bar">
    <div><h1>TigerForge<span class="mini">虎铸 · 项目 AI 开发平台</span></h1>
    <div class="sub" id="phys" style="margin:4px 0 0">—</div></div>
    <div id="userbar"></div>
  </div>

  <!-- 管理项目 -->
  <div id="v-manage">
    <div class="panel" style="display:flex;align-items:center;justify-content:space-between;gap:12px;flex-wrap:wrap">
      <div><b>我的项目实例</b> <span class="muted" id="cnt"></span></div>
      <button class="bigbtn" onclick="showCreate()">＋ 创建项目</button>
    </div>
    <div id="list"></div>
  </div>

  <!-- 创建（选规格） -->
  <div id="v-create" style="display:none">
    <div class="panel">
      <div class="bar"><b>创建项目 —— 选择实例</b><button class="ghost" onclick="showManage()">← 返回</button></div>
      <div class="row">
        <div><label>项目名</label><input id="name" placeholder="例如：每日账本"></div>
        <div><label>实例规格</label><select id="spec" onchange="renderPrice()"></select></div>
        <div><label>计费周期</label><select id="cycle" onchange="renderPrice()">
          <option value="month">月租</option><option value="year">包年（算力 8 折）</option></select></div>
        <div><label>硬盘（GB，HDD 分项）</label><select id="disk" onchange="renderPrice()"></select></div>
        <div><label>带宽（M，分配值不另计费）</label><select id="bw"></select></div>
      </div>
      <label>AI 模型</label>
      <select id="modelsel" onchange="document.getElementById('ai').style.display=this.value==='__custom__'?'block':'none'"></select>
      <div id="ai" style="display:none"><div class="row">
        <div><label>API 地址 baseUrl</label><input id="baseUrl" placeholder="https://…/v1"></div>
        <div><label>API Key</label><input id="apiKey" placeholder="sk-…（掩码=不改）"></div>
        <div><label>模型名</label><input id="model" placeholder="mimo-v2.6-flash"></div></div></div>
      <label>初始提示词（Agent 拿到实例后干什么）</label>
      <textarea id="prompt" placeholder="例：做一个每日账本网页：可增删记录、按月统计、数据存本地；界面简洁中文；自测要真启动服务并验证"></textarea>
      <table class="bill" id="ptable"></table>
      <div style="margin-top:14px;display:flex;gap:10px;align-items:center">
        <button class="bigbtn" onclick="showPay()">下一步：确认支付</button>
        <span class="muted" id="createmsg"></span>
      </div>
    </div>
  </div>

  <!-- 支付确认 -->
  <div id="v-pay" style="display:none">
    <div class="panel" style="max-width:560px">
      <div class="bar"><b>确认支付</b><button class="ghost" onclick="showCreate()">← 返回修改</button></div>
      <table class="bill" id="paytable"></table>
      <div class="muted" id="paywarn" style="margin-top:8px"></div>
      <div style="margin-top:16px;display:flex;gap:10px;align-items:center">
        <button class="bigbtn" id="paybtn" onclick="doPay()">支付并创建实例</button>
        <span class="muted" id="paymsg"></span>
      </div>
      <div class="muted" style="margin-top:10px">支付成功后：先创建虚拟机并安装 Windows（实例模式为 host 时跳过），
      然后 Agent 自动开始构建 —— 完成即进入对话界面。</div>
    </div>
  </div>

  <!-- Agent 使用（详情+对话） -->
  <div id="v-agent" style="display:none">
    <div class="bar"><b>Agent 界面</b><button class="ghost" onclick="showManage()">← 返回管理项目</button></div>
    <div id="detail" class="muted">选择左侧项目</div>
  </div>

  <!-- 管理后台（/admin，管理员专用 —— 用户面不含任何管理控件） -->
  <div id="v-admin" style="display:none">
    <div class="panel" style="display:flex;justify-content:space-between;align-items:center;flex-wrap:wrap;gap:10px">
      <div><b style="font-size:17px">TigerForge 后台</b>
        <span class="muted" id="admintitle">财务 / 独立IP池 / 补扣 / 全部用户与项目</span></div>
      <a href="/platform" class="muted">← 返回用户界面</a>
    </div>
    <div class="panel">
      <span class="eyebrow">财务</span>
      <div class="row">
        <div><label>充值 → 用户名</label><input id="tuuser"></div>
        <div><label>金额（元）</label><input id="tuyuan" type="number" min="0" step="0.01"></div>
        <div style="align-self:end"><button class="ghost" onclick="topup()">充值</button></div>
      </div>
      <div class="row" style="margin-top:6px">
        <div><label>计费补扣（期，1..12）</label><input id="tickp" type="number" min="1" max="12" step="1" value="1"></div>
        <div style="align-self:end"><button class="ghost" onclick="tickNow()">立即补扣</button></div>
      </div>
      <div class="muted" id="adminmsg" style="margin-top:8px"></div>
    </div>
    <div class="panel">
      <span class="eyebrow">独立 IP 池</span>
      <div class="row">
        <div><label>加入一个</label><input id="ipadd" placeholder="127.0.0.55（演示）或已绑到网卡的 IP"></div>
        <div style="align-self:end"><button class="ghost" onclick="ipAdd()">加入池</button></div>
      </div>
      <div class="muted" id="iprow" style="margin-top:6px">IP 池: —</div>
    </div>
    <div class="panel"><span class="eyebrow">全部用户</span><div id="admusers" class="muted">—</div></div>
    <div class="panel"><span class="eyebrow">全部项目实例</span><div id="admprojects" class="muted">—</div></div>
  </div>
</div>
<script>
let OPTS=null,SEL=null,ME=null,ADM=false,PRICE={},IPOPT={},VIEW='landing';
const $=id=>document.getElementById(id);
async function j(url,opt){const r=await fetch(url,opt);let d=null;try{d=await r.json()}catch(e){}
 if(!r.ok)throw new Error((d&&d.error)||r.status);return d}
function esc(s){return (s||'').replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]))}
function yuan(c){return c==null?'—':'¥'+(Number(c)/100).toFixed(2)}
const statusText=s=>({created:'实例就绪',provisioning:'创建虚拟机/装 Windows…',building:'Agent 构建中',testing:'自测中',deploying:'部署中',live:'已上线',failed:'失败',stopped:'已停止'})[s]||s;
const kindText=k=>({web:'网页','client':'客户端','three-tier':'三端','unknown':'未知'})[k]||k;

/* ---------- 视图切换 ---------- */
function show(v){VIEW=v;['v-landing','v-app','v-manage','v-create','v-pay','v-agent','v-admin'].forEach(id=>{const el=$(id);if(el)el.style.display='none'});
 if(v==='landing'){$('v-landing').style.display='';return}
 $('v-app').style.display='';
 ['v-manage','v-create','v-pay','v-agent'].forEach(id=>$(id).style.display='none');
 $('v-'+v).style.display=''}
function showManage(){show('manage');refresh()}
function showCreate(){show('create');renderPrice()}
function showPay(){renderPay();show('pay')}
function openAgent(id){show('agent');detail(id);startDetailPolling(id)}
function startDetailPolling(id){
 if(window._detailTimer)clearInterval(window._detailTimer);
 window._detailTimer=setInterval(async()=>{
  if(SEL!==id||VIEW!=='agent'){clearInterval(window._detailTimer);window._detailTimer=null;return}
  try{const p=await j('/api/platform/projects/'+id,{credentials:'same-origin'});
   if(!p.busy&&['building','provisioning','testing','deploying'].indexOf(p.status)<0) detail(id);
  }catch(e){}
 },3000);
}

/* ---------- 登录/注册 ---------- */
async function authMe(){try{const r=await fetch('/api/auth/me',{credentials:'same-origin'});return await r.json()}catch(e){return {authEnabled:false}}}
function renderLanding(){
 const reg=!ME.authEnabled;
 $('authmsg').textContent='';            // 视图重画时清残留提示（否则留着旧文案）
 $('lt').textContent=reg?'创建管理员账号':'登录 TigerForge';
 $('btnreg').style.display=reg?'':'none';
 $('lsub').textContent=reg?'还没有任何账号 —— 第一个即管理员（部署者本人）':'用管理员分配的账号登录；登录后管理与创建你的项目实例';
 $('lprice').innerHTML=['1C1G ¥11/月','2C2G ¥20/月','4C8G ¥38/月','8C16G ¥69/月']
  .map(x=>'<span class="chip">'+x+'</span>').join('')
  +'<span class="chip free">包年算力8折</span><span class="chip">IP ¥6/月</span>'
  +'<span class="chip">HDD ¥0.06/G/月</span><span class="chip">流量 ¥0.5/GB</span>';
 if(reg)$('authhint').textContent='';else $('authhint').textContent='';
}
async function authLogin(){
 $('authmsg').textContent='登录中…';
 try{const r=await fetch('/api/auth/login',{method:'POST',headers:{'Content-Type':'application/json'},credentials:'same-origin',
  body:JSON.stringify({username:$('authuser').value,password:$('authpw').value})});
  const d=await r.json();
  if(!r.ok||!d.success){$('authmsg').textContent=d.error||'登录失败';return}
  await boot();
 }catch(e){$('authmsg').textContent=e.message}
}
async function authRegister(){
 $('authmsg').textContent='创建中…';
 try{const r=await fetch('/api/auth/register',{method:'POST',headers:{'Content-Type':'application/json'},credentials:'same-origin',
  body:JSON.stringify({username:$('authuser').value,password:$('authpw').value})});
  const d=await r.json();
  if(!r.ok||!d.success){$('authmsg').textContent=d.error||'创建失败';return}
  // 【注册成功必须立刻有反馈并前进】原实现直接 await boot() —— authmsg 还挂着
  // "创建中…"、又没有登录态，画面纹丝不动 = 用户报的"一直卡着" ✗✗✗
  // （实证: Leo 账号 2026-10-20 20:30 已建成功，只是界面没说）。改成: 同凭据**自动登录**。
  $('authmsg').textContent='✓ 创建成功，正在登录…';
  await authLogin();
 }catch(e){$('authmsg').textContent=e.message}
}
async function logout(){try{await fetch('/api/auth/logout',{method:'POST',credentials:'same-origin'})}catch(e){}location.reload()}

/* ---------- 价格（镜像服务端公式） ---------- */
function priceOf(spec,cycle){const t=(cycle==='year'?PRICE.year:PRICE.month)||{};
 if(t[spec]!=null)return t[spec];
 const m=String(spec||'').match(/^(\d+)C(\d+)G$/);if(!m)return null;
 const base=500*(+m[1])+600*(+m[2]);
 return cycle==='year'?Math.round(base*12*0.8):base}
function extrasCents(diskGb,hasIp){return diskGb*(PRICE.diskGbMonth||6)+(hasIp?(PRICE.ipMonth||600):0)}
function hasIpPool(){return IPOPT&&IPOPT.configured}
function formState(){return {name:$('name').value||'未命名项目',spec:$('spec').value,cycle:$('cycle').value,
 disk:+$('disk').value,bw:+$('bw').value,prompt:$('prompt').value}}
function totalOf(st){const ip=hasIpPool();
 return priceOf(st.spec,st.cycle)+extrasCents(st.disk,ip)*(st.cycle==='year'?12:1)}
function renderPrice(){
 const st=formState();const ip=hasIpPool();
 const c=priceOf(st.spec,st.cycle);
 const months=st.cycle==='year'?12:1;
 const rows=[
  ['实例算力'+(st.cycle==='year'?`（包年 8 折，365 天）`:`（月租，30 天）`),yuan(c)],
  ['HDD 硬盘 '+st.disk+'G × ¥0.06/G/月'+(months>1?' × 12 月':''),yuan(extrasCents(st.disk,false)*months)],
  [ip?('独立公网 IP × ¥6/个/月'+(months>1?' × 12 月':'')):'独立公网 IP（池未配置，不分配不计费）',yuan(ip?(PRICE.ipMonth||600)*months:0)],
  ['带宽 '+st.bw+'M（分配值，不另计费）','—'],
  ['出站流量（¥0.5/GB，按周期结算）','用后结算'],
  ['<b>首期应付</b>','<b>'+yuan(totalOf(st))+'</b>'],
  ['当前余额',yuan(ME?ME.balance:null)]];
 $('ptable').innerHTML=rows.map(r=>'<tr><td>'+r[0]+'</td><td class="n">'+r[1]+'</td></tr>').join('');
 const btn=document.querySelector('#v-create button.bigbtn');
 if(btn){btn.disabled=!!(ME&&ME.authEnabled&&c!=null&&ME.balance<totalOf(st))}
 const cm=$('createmsg');
 if(cm)cm.textContent=(ME&&ME.authEnabled&&ME.balance<totalOf(st))?'余额不足 —— 先找管理员充值':'';
}
function renderPay(){
 const st=formState();const ip=hasIpPool();const months=st.cycle==='year'?12:1;
 const base=priceOf(st.spec,st.cycle);
 const diskC=extrasCents(st.disk,false)*months;
 const ipC=ip?(PRICE.ipMonth||600)*months:0;
 const total=base+diskC+ipC;
 const rows=[
  ['项目名',esc(st.name)],
  ['实例规格',esc(st.spec)],
  ['计费周期',st.cycle==='year'?'包年（365 天，算力 8 折）':'月租（30 天）'],
  ['算力'+(st.cycle==='year'?'（包年 8 折）':'（月租）'),yuan(base)],
  ['HDD 硬盘 '+st.disk+'G'+(months>1?' × 12 月':''),yuan(diskC)],
  [ip?'独立公网 IP'+(months>1?' × 12 月':''):'独立公网 IP（池未配置）',yuan(ipC)],
  ['出站流量 ¥0.5/GB','按使用周期结算'],
  ['<b>应付合计</b>','<b>'+yuan(total)+'</b>'],
  ['账户余额',yuan(ME?ME.balance:null)],
  ['支付后余额',yuan(ME&&ME.authEnabled?ME.balance-total:null)]];
 $('paytable').innerHTML=rows.map(r=>'<tr><td>'+r[0]+'</td><td class="n">'+r[1]+'</td></tr>').join('');
 $('paywarn').textContent=(ME&&ME.authEnabled&&ME.balance<total)?'余额不足，无法支付 —— 请先让管理员充值。':'';
 $('paybtn').disabled=!!(ME&&ME.authEnabled&&ME.balance<total);
}
async function doPay(){
 const st=formState();
 if(!st.prompt.trim()){$('paymsg').textContent='缺少初始提示词 —— 返回上一步填写';return}
 $('paybtn').disabled=true;$('paymsg').textContent='支付中…';
 try{const d=await j('/api/platform/projects',{method:'POST',headers:{'Content-Type':'application/json'},credentials:'same-origin',
   body:JSON.stringify({name:st.name,prompt:st.prompt,spec:st.spec,cycle:st.cycle,
    bandwidthMb:st.bw,diskGb:st.disk,
    aiApi:$('modelsel').value==='__custom__'?{baseUrl:$('baseUrl').value,apiKey:$('apiKey').value,model:$('model').value}
      :($('modelsel').value?{model:$('modelsel').value}:{})})});
  ME.balance=null;await refreshMe();
  $('paymsg').textContent='支付成功 ✓ 正在创建实例…';
  $('prompt').value='';
  openAgent(d.id);
 }catch(e){$('paymsg').innerHTML='<span class="err">'+esc(e.message)+'</span>'}
 finally{$('paybtn').disabled=false}
}
async function refreshMe(){try{ME=await authMe();renderUserbar()}catch(e){}}

/* ---------- 管理：列表 ---------- */
function renderUserbar(){
 if(!ME||!ME.username){$('userbar').innerHTML='';return}
 ADM=!!ME.admin;
 $('userbar').innerHTML=
  '<span class="uchip"><span class="udot">'+esc((ME.username||'?').slice(0,1).toUpperCase())+'</span>'
  +'<b>'+esc(ME.username)+'</b>'+(ADM?'<span class="muted">管理员</span>':'')
  +'<span class="bal">'+yuan(ME.balance)+'</span>'
  +(ADM?'<a href="/admin" class="ghost" style="margin:0;padding:4px 12px;text-decoration:none">后台</a>':'')
  +'<button class="ghost" onclick="logout()" style="margin:0;padding:4px 12px">退出</button></span>';
 if(ADM){$('tuuser').value=ME.username;refreshAdmin()}
}
async function refresh(){try{const d=await j('/api/platform/projects',{credentials:'same-origin'});
 $('cnt').textContent='（'+d.items.length+' 个）';
 $('list').innerHTML=d.items.map(p=>card(p,d.busy)).join('')||'<div class="muted">还没有项目 —— 点上方「＋ 创建项目」开始</div>'}catch(e){}}
function card(p,busy){
 return `<div class="card"><b>${esc(p.name)}</b> <span class="badge b-${p.status}">${esc(statusText(p.status))}</span>
 <div class="muted">${esc(String(p.spec||''))} · ${esc(String(p.cycle==='year'?'包年':'月租'))} · 带宽 ${esc(String(p.bandwidthMb||'-'))}M · 硬盘 ${esc(String(p.diskGb))}G${p.kind?' · '+kindText(p.kind):''}${ME&&p.owner&&p.owner!==ME.username?' · 👤'+esc(p.owner):''}${p.ip?' · IP '+esc(p.ip):''} · ${p.createdAt}</div>
 <div style="margin-top:8px"><button class="ghost" onclick="openAgent('${p.id}')">对话 / 详情</button>
 ${p.webUrl?`<button class="ghost" onclick="window.open('/serve/${p.id}/','_blank')">打开网页</button>`:''}
 ${p.dlUrl?`<button class="ghost" onclick="window.open('/dl/${p.id}/','_blank')">下载页</button>`:''}
 <button class="ghost" onclick="stopP('${p.id}')">停止</button></div></div>`}
async function stopP(id){await j('/api/platform/projects/'+id+'/stop',{method:'POST'});refresh()}
async function redeploy(id){await j('/api/platform/projects/'+id+'/redeploy',{method:'POST'});refresh();detail(id)}
async function rebuildP(id){await j('/api/platform/projects/'+id+'/rebuild',{method:'POST'});refresh();detail(id)}
async function delP(id){
 if(!confirm('删除该实例？磁盘、配额、独立 IP 全部回收，账单保留，不可恢复'))return;
 try{await j('/api/platform/projects/'+id+'/delete',{method:'POST'});
  SEL=null;$('detail').innerHTML='<div class="muted">已删除 ✓</div>';refresh()}
 catch(e){alert(e.message||'删除失败')}
}

/* ---------- Agent 界面：详情+对话 ---------- */
async function detail(id){SEL=id;const p=await j('/api/platform/projects/'+id,{credentials:'same-origin'});
 const t=p.test||{};
 // 对话永久存储的读取面: 打开项目就把历史灌回终端面板（重启/换机都在 —— jsonl+MySQL 双写）
 let hist=[];try{const hm=await j('/api/platform/projects/'+id+'/messages',{credentials:'same-origin'});hist=hm.rows||[]}catch(e){}
 const paneInit=hist.length?hist.map(m=>m.role==='user'
  ?'<div style="margin-bottom:7px"><span style="color:#e3b341">❯</span> '+esc(m.text)+'</div>'
  :'<div style="margin-bottom:7px"><span style="color:#57606a">'+esc(String(m.at||''))+'</span> '+esc(m.text)+'</div>').join('')
  :(p.busy?'<span class="muted">实例正在构建/供给 —— 完成后这里直接对话（本面板每 5 秒自动刷新）</span>'
          :'<span class="muted">（暂无对话记录 —— 输入后回车开始；对话永久入库）</span>');
 $('detail').innerHTML=`<div class="card"><b>${esc(p.name)}</b> <span class="badge b-${p.status}">${esc(statusText(p.status))}</span>
 <div class="muted">实例 ${esc(String(p.spec||''))} · ${esc(String(p.cycle||'month'))} · 带宽 ${esc(String(p.bandwidthMb||'-'))}M · 硬盘 ${esc(String(p.diskGb))}G · 会话 ${esc(p.sessionId)}</div>
 <div class="muted">已付至 ${p.paidUntil?new Date(p.paidUntil*1000).toLocaleString():'—'} · 出站流量 ${((p.egressBytes||0)/1048576).toFixed(2)} MB（未结 ${(((p.egressBytes||0)-(p.egressBilledBytes||0))/1048576).toFixed(2)} MB）</div>
 ${p.vm?`<div class="muted">虚拟机 <b>${esc(p.vm)}</b>（${esc(p.vmMode||'')}）${p.vmIp?' · 客户机 IP '+esc(p.vmIp):''}</div>`:''}
 ${p.ipInfo?`<div class="muted">独立 IP <b>${esc(p.ipInfo.ip)}</b> —— ${p.ipInfo.onMachine?'✓ 本机已绑定':'⚠ 未在本机网卡上（需管理员 netsh 绑定）'}</div>`:''}
 ${!p.ip&&(IPOPT&&!IPOPT.configured)?'<div class="muted">⚠ IP 池未配置 —— 管理端加入 IP 后，新购实例会分到独立地址</div>':''}
 ${t.kind?`<div class="muted">自测: ${esc(kindText(t.kind))}${t.http!==null?' · HTTP '+esc(String(t.http)):''}${t.title?' · 标题「'+esc(t.title)+'」':''}</div>`:''}
 ${p.webUrl?`<div>网页：<a href="${p.webUrl}" target="_blank">${esc(p.webUrl)}</a></div>`:''}
 ${p.dlUrl?`<div>下载页：<a href="${p.dlUrl}" target="_blank">${esc(p.dlUrl)}</a></div>`:''}
 ${p.error?`<div class="err">${esc(p.error)}</div>`:''}
 <div class="muted" style="margin-top:6px">隔离说明：工作目录即本实例全部可见空间（越界路径被沙箱拒绝）；shell 引用实例外绝对路径也会被拦。
 带宽为分配值；出站流量按平台代发字节计（¥0.5/GB，周期结算）。</div>
 <div style="margin-top:8px"><button class="ghost" onclick="rebuildP('${p.id}')">重新构建</button>
 <button class="ghost" onclick="redeploy('${p.id}')">重新部署</button>
 <button class="ghost" onclick="stopP('${p.id}');detail('${p.id}')">停止</button>
 <button class="danger" onclick="delP('${p.id}')">删除实例</button></div>
 ${p.buildReply?`<details><summary class="muted">Agent 结论</summary><div class="muted">${esc(p.buildReply)}</div></details>`:''}
 </div>
 <div class="card" style="padding:0;overflow:hidden">
 <div style="background:#0a0d12;border-bottom:1px solid var(--line);padding:8px 14px;display:flex;justify-content:space-between;align-items:center">
  <b style="font-family:Consolas,'Courier New',monospace;letter-spacing:.06em;color:#ffb638">❯ TigerForge · Agent 终端</b>
  <span class="muted" id="chatstat" style="font-family:Consolas,'Courier New',monospace">${p.busy?'构建/供给中…':'就绪 · 回车发送'}</span></div>
 <div id="chatpane" style="height:290px;overflow:auto;background:#0a0d12;padding:12px 14px;font:13px/1.7 Consolas,'Courier New',monospace;white-space:pre-wrap">${paneInit}</div>
 <div style="display:flex;background:#0f141a;border-top:1px solid var(--line)">
  <span style="color:#ffb638;padding:10px 0 0 14px;font-family:Consolas,monospace">❯</span>
  <textarea id="chatin" rows="2" style="flex:1;background:transparent;border:0;color:#e6edf3;font:13px/1.6 Consolas,'Courier New',monospace;resize:none;outline:none;padding:9px 10px" ${p.busy?'disabled':''} placeholder="${p.busy?'实例就绪后可输入…':'输入指令，回车发送（Shift+Enter 换行）'}" onkeydown="chatKey(event)"></textarea>
  <button id="chatsend" onclick="send()" ${p.busy?'disabled':''} style="align-self:stretch;border-radius:0;padding:0 24px">发送</button></div>
 </div>
 <div class="card"><span class="eyebrow">构建 / 部署日志</span><pre id="dlog">${esc(p.log||'（暂无）')}</pre></div>`;
 fetch('/api/platform/billing',{credentials:'same-origin'}).then(r=>r.json()).then(d=>{
  if(!d||!d.enabled||!(d.rows||[]).length)return;
  const box=document.createElement('div');box.className='card';
  box.innerHTML='<b>账单（近 '+d.rows.length+' 条）· 余额 '+yuan(d.balance)+'</b>'
   +'<table class="bill">'+d.rows.slice(0,8).map(r=>'<tr><td>'+esc(r.at)+'</td><td>'+esc(r.kind)+'</td><td class="n">'
     +(r.cents>0?yuan(r.cents):'—')+'</td><td class="muted">'+esc(r.note||'')+'</td></tr>').join('')+'</table>';
  $('detail').appendChild(box);
 }).catch(()=>{});
 if(p.busy)setTimeout(()=>{if(SEL===p.id)detail(p.id)},5000)}
/* CLI 风格终端对话（对齐以前终端界面的手感: ❯ 提示符 / 时间戳 / 状态行 / 回车发送） */
function chatKey(e){if(e.key==='Enter'&&!e.shiftKey){e.preventDefault();send()}}
function chatAppend(role,text,cls){
 const el=$('chatpane');if(!el)return;
 if(el.querySelector('.muted')&&role==='me'){el.innerHTML=''}   // 清"构建中"占位
 const d=document.createElement('div');d.style.marginBottom='7px';
 if(role==='me'){d.innerHTML='<span style="color:#e3b341">❯</span> '+esc(text)}
 else if(cls){d.innerHTML='<span style="color:'+cls+'">'+esc(text)+'</span>'}
 else{d.innerHTML='<span style="color:#57606a">'+new Date().toLocaleTimeString()+'</span> '+esc(text)}
 el.appendChild(d);el.scrollTop=el.scrollHeight}
async function send(){const id=SEL,ta=$('chatin'),msg=ta.value.trim();if(!msg)return;
 ta.value='';$('chatsend').disabled=true;
 const st=$('chatstat');if(st)st.textContent='思考中…（云端一轮可能要几分钟）';
 chatAppend('me',msg);
 const t0=Date.now();
 try{const d=await j('/api/platform/projects/'+id+'/chat',{method:'POST',headers:{'Content-Type':'application/json'},credentials:'same-origin',body:JSON.stringify({message:msg})});
  chatAppend('ai',(d.reply||'(无回复)')+(d.note?'\n['+d.note+']':''));
  if(st)st.textContent='就绪 · 本轮 '+Math.round((Date.now()-t0)/1000)+'s';
  // 注意: 不整页重绘 detail —— 否则刚打的对话记录被清空（CLI 手感全靠这块面板）
 }catch(e){chatAppend('ai','✗ '+e.message,'#f85149');if(st)st.textContent='就绪（上轮失败）'}
 finally{$('chatsend').disabled=false}}

/* ---------- 管理端 ---------- */
async function adminPost(path,body){
 try{const r=await fetch(path,{method:'POST',headers:{'Content-Type':'application/json'},credentials:'same-origin',body:JSON.stringify(body)});
  return {ok:r.ok,d:await r.json()}}catch(e){return {ok:false,d:{error:e.message}}}
}
async function topup(){
 const x=await adminPost('/api/platform/admin/topup',{username:$('tuuser').value,yuan:$('tuyuan').value});
 $('adminmsg').innerHTML=x.ok?('<span style="color:#3fb950">✓ 已充值，余额 '+yuan(x.d.balance)+'</span>'):('<span class="err">'+esc(x.d.error||'失败')+'</span>');
 refreshMe();
}
async function ipAdd(){
 const x=await adminPost('/api/platform/admin/ips',{ip:$('ipadd').value});
 $('adminmsg').innerHTML=x.ok?'<span style="color:#3fb950">✓ 已加入 IP 池</span>':('<span class="err">'+esc(x.d.error||'失败')+'</span>');
 refreshAdmin();
}
async function tickNow(){
 const x=await adminPost('/api/platform/billing/tick',{periods:+$('tickp').value||1});
 $('adminmsg').innerHTML=x.ok?('✓ 扣费 '+(x.d.charged||[]).length+' 台 / 停机 '+(x.d.stopped||[]).length+' 台'):('<span class="err">'+esc(x.d.error||'失败')+'</span>');
 refresh();refreshMe();
}
async function refreshAdmin(){
 try{const r=await fetch('/api/platform/admin/ips',{credentials:'same-origin'});const d=await r.json();
  if(!r.ok){$('iprow').textContent='IP 池: '+(d.error||'读取失败')}
  else{const rows=(d.pool||[]).map(x=>x.ip+(x.used?'（已分配…）':(x.onMachine?'（本机✓可用）':'（未绑到网卡 ⚠）'))).join(' · ');
  $('iprow').innerHTML='IP 池: '+(rows||'空 —— 新购实例将不分到独立 IP')+'<br><span class="muted">'+esc(d.hint||'')+'</span>'}
 }catch(e){}
 try{const r=await fetch('/api/platform/admin/users',{credentials:'same-origin'});const d=await r.json();
  if(r.ok){$('admusers').innerHTML='<table class="bill"><tr><th>用户</th><th>角色</th><th class="n">余额</th><th>注册于</th></tr>'
   +(d.users||[]).map(u=>'<tr><td>'+esc(u.username)+'</td><td>'+(u.admin?'管理员':'租户')+'</td><td class="n">'+yuan(u.balance)+'</td><td class="muted">'+esc(String(u.created||''))+'</td></tr>').join('')+'</table>'}
  else{$('admusers').textContent=d.error||'读取失败'}
 }catch(e){}
 try{const r=await fetch('/api/platform/admin/projects',{credentials:'same-origin'});const d=await r.json();
  if(r.ok){$('admprojects').innerHTML='<table class="bill"><tr><th>项目</th><th>属主</th><th>规格</th><th>状态</th><th>独立IP</th><th>到期</th></tr>'
   +(d.rows||[]).map(p=>'<tr><td>'+esc(String(p.name))+' <span class="muted">'+esc(String(p.id||'').slice(-6))+'</span></td><td>'+esc(String(p.owner||'-'))+'</td><td>'+esc(String(p.spec||'-'))+'</td><td>'+esc(String(p.status||''))+'</td><td>'+esc(String(p.ip||'-'))+'</td><td class="muted">'+esc(String(p.paidUntil||'-'))+'</td></tr>').join('')+'</table>'}
  else{$('admprojects').textContent=d.error||'读取失败'}
 }catch(e){}
}

/* ---------- 信息/启动 ---------- */
async function loadInfo(){const i=await j('/api/platform/info',{credentials:'same-origin'});OPTS=i.options;PRICE=i.pricing||{};IPOPT=i.ipPool||{};
 const mode=i.instanceMode==='host'?'<b>主机进程模式</b>':(i.vbox&&i.vbox.available?'<b>虚拟机模式</b>（'+esc(i.vbox.reason||'')+'）':'<span style="color:#f85149">⚠ 虚拟机模式但 '+esc((i.vbox&&i.vbox.reason)||'VBox 不可用')+'</span>');
 const db='账号库: '+(i.accountDb==='json'?'JSON 文件':'<b>'+esc(i.accountDb)+'</b>');
 $('phys').innerHTML=`物理机 <b>${i.physical.cores}</b> 核 / <b>${i.physical.ramMb}</b> MB / 磁盘 <b>${i.physical.diskGb}</b> GB · ${i.physical.os||''}
  · 已分配 <b>${i.used.cpu}</b> 核 / <b>${i.used.memMb}</b> MB / 带宽 <b>${i.used.bwMb||0}</b> M（${i.used.count} 个实例） · ${mode} · ${db}
  ${i.tenantLock?' · <b style="color:#3fb950">🔒 租户锁定已开启</b>':' · <b style="color:#fbbf24">⚠ 未开租户锁定（对外服务置 LION_TENANT_LOCK=1）</b>'}
  ${i.degraded?' · <b style="color:#f85149">⚠ '+esc(i.degraded)+'</b>':''}`;
 fill('spec',i.options.specs);fill('disk',i.options.diskGb);fill('bw',i.options.bandwidthMb);
 $('spec').value=(i.options.specs||[]).includes('2C2G')?'2C2G':(i.options.specs||['1C1G'])[0];
 $('disk').value='20';$('bw').value='10';
 const fallback='<option value="">沿用当前已配置的模型</option><option value="__custom__">自定义（baseUrl / API Key / 模型名）</option>';
 try{const ml=await j('/api/models/cloud',{credentials:'same-origin'});
  const ids=(Array.isArray(ml&&ml.data)?ml.data:[]).map(m=>typeof m==='string'?m:String((m&&m.id)||'')).filter(Boolean);
  $('modelsel').innerHTML='<option value="">沿用当前已配置的模型</option>'+ids.map(v=>`<option>${esc(v)}</option>`).join('')+'<option value="__custom__">自定义（baseUrl / API Key / 模型名）</option>';}
 catch(e){$('modelsel').innerHTML=fallback}
 if(ME&&ME.authEnabled&&!ME.admin){$('modelsel').innerHTML='<option value="">服务端统一配置的模型</option>';$('modelsel').disabled=true}
}
function fill(id,arr){const s=$(id);if(s)s.innerHTML=(arr||[]).map(v=>`<option>${v}</option>`).join('')}
async function boot(){
 ME=await authMe();
 if(!ME||!ME.username){renderLanding();show('landing');return}
 renderUserbar();
 // 【前台/后台分开】/admin 路径 = 管理后台视图；租户访问被服务端角色门 403 挡在
 // 页面之前（这里只兜底"管理员身份失效"的边）
 const wantAdmin=location.pathname.indexOf('/admin')===0;
 if(wantAdmin){
  if(!ADM){$('admintitle').textContent='当前账号不是管理员 —— 后台不可用'}
  show('v-admin');await loadInfo();refreshAdmin();return
 }
 show('manage');
 await loadInfo();
 refresh();
 if(!window._iv){window._iv=true;setInterval(refresh,4000);
  setInterval(()=>{if(SEL&&VIEW==='agent'){fetch('/api/platform/projects/'+SEL+'/log',{credentials:'same-origin'}).then(r=>r.text()).then(t=>{const el=$('dlog');if(el)el.textContent=t||'（暂无）'}).catch(()=>{})}},3000);
  // 标签页回前台立即刷新 —— 后台标签会被节流，用户切回来盯着几秒前的旧画面
  // 以为"构建中卡住了"（连环报障实证 ✗✗✗✗✗）
  document.addEventListener('visibilitychange',()=>{if(!document.hidden){
   refresh();refreshMe();
   if(SEL&&VIEW==='agent')detail(SEL);
   if(location.pathname.indexOf('/admin')===0)refreshAdmin();
  }})}
}
boot();
</script></body></html>"""
