#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Polymas（智慧树）智能体课程 全自动看课脚本（纯 HTTP，无需浏览器）
================================================================

作者：古月波
仓库：https://github.com/GuYueBo2008/NJUPT_Zhidao_Autopass
协议：MIT License
声明：仅供学习交流使用，禁止倒卖本二进制文件！
     本程序不会保存账号密码，也不会向任何第三方上传个人信息。

一条命令走完全流程：
    账号密码登录(南邮 SSO) -> 智慧树 CAS -> 换取 ai-poly -> 选课 -> 逐视频上报 -> 复核

用法
----
    python3 polymas_auto.py                        # 全自动交互：登录 -> 选课 -> 看课(带进度条)
    python3 polymas_auto.py --select               # 同上，强制进入交互选课（非终端环境也可）
    python3 polymas_auto.py --list                 # 登录并列出课程
    python3 polymas_auto.py --course 1             # 看第 1 门课（序号 / courseId / 名称片段）
    python3 polymas_auto.py --course 1 --force     # 忽略已完成，全部重报
    python3 polymas_auto.py --all                  # 看账号下所有课
    python3 polymas_auto.py --course 1 --dry-run   # 只看，不上报
    python3 polymas_auto.py --chunk 30             # 每 30 秒一片上报（默认 60）
    python3 polymas_auto.py --no-color             # 纯文本输出（旧终端 / 重定向日志）

交互选课支持多选：输入 1,3 看第 1、3 门；输入 0 看全部；q 退出。
看课过程在终端显示彩色进度条，非终端环境则逐行打印百分比。

上报节奏（避免"观看时间露馅"）
    视频按 --chunk 切成若干分片逐步上报，而不是一次跳满 100%：
    每片的 startDate/endDate 差值与该片观看时长严格相等，相邻分片首尾相接，
    多个视频串成一条连续时间线，最后一片结束时间贴近真实当前时间；
    分片长度与间隔加入随机抖动，避免固定节奏的机器特征。
    --chunk 0 表示不分片（一次上报整段，最容易被识别，不建议）。
    --realtime 可强制按真实时间发送：等到每片真的"看完"才上报，于是"请求到达时间"与
    上报的观看时间基本重合（整批耗时≈视频总时长；单线程=按顺序真实播放，多线程=多视频同时真实播放）。
    该开关既可用命令行 --realtime 指定，也可在选课界面输入 r / safe 随时切换
    （单独输入或与序号连着写都可以，如 r、1r、1,r、safe；输入法打成全角也会自动转半角）。
看完不会自动退出：可继续选择其它课程，输入 q 才结束；结束时会打印错误汇总与日志路径。
同意免责声明后等 2 秒自动进入程序；首页→登录→选课→看课→返回选课 等功能切换会自动清屏。
多线程并发上报（--threads，默认 8、最大 32）：每个视频一个线程同步推送，视频内部的分片仍按顺序串行发送。

登录信息（不再内置账号）
    启动时交互询问 账号/学号 与 密码（密码以星号回显，输入法全角字符会自动转成半角英文）；
    也可用命令参数  --user <账号> --pass <密码>
    或环境变量     ZHS_USER / ZHS_PASS
    本工具仅适配南邮 SSO，学校无需（也无法）指定，其它学校的 CAS 认证方式未知。

诊断与日志
    运行中每步都会写入日志文件（默认与程序同目录的 polymas_auto.log）；
    发生错误时控制台即时提示，结束时汇总错误清单，堆栈详见日志文件。

已有 token 时可跳过登录（跳过 SSO，直接看课）
    --token eyJ0eXAi...   或   export AIPOLY_TOKEN='eyJ0eXAi...'

依赖：requests、cryptography
    pip install requests cryptography
"""

import argparse
import json
import os
import random
import re
import sys
import tempfile
import threading
import time
import traceback
import unicodedata
from concurrent.futures import ThreadPoolExecutor, as_completed
from urllib.parse import quote, urlparse, parse_qs

import requests
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes


def _harden_console_encoding():
    """Windows 控制台中文输出加固：切到 UTF-8 代码页并强制 stdout/stderr 用 UTF-8。"""
    try:
        import ctypes
        ctypes.windll.kernel32.SetConsoleOutputCP(65001)
        ctypes.windll.kernel32.SetConsoleCP(65001)
    except Exception:
        pass
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8", errors="replace")
        except Exception:
            pass


# ============================== 终端配色 ==============================

APP_NAME = "Polymas 自动看课助手"
APP_VERSION = "v1.1.2"
APP_AUTHOR = "古月波"
APP_REPO = "github.com/GuYueBo2008/NJUPT_Zhidao_Autopass"
APP_LICENSE = "MIT License"
# 本工具只适配南邮统一身份认证；其它学校的 CAS 认证流程尚未验证，不保证可用
APP_SCHOOL = "南京邮电大学（南邮）"

USE_COLOR = False          # 是否启用彩色输出
USE_VT = False             # 终端是否支持 ANSI 转义（清屏依赖它）
LINE = "-" * 58
BOX_W = 60                 # 主页信息框宽度

_RESET = "\033[0m"
C_RED = "\033[91m"
C_GREEN = "\033[92m"
C_YELLOW = "\033[93m"
C_BLUE = "\033[94m"
C_MAGENTA = "\033[95m"
C_CYAN = "\033[96m"
C_WHITE = "\033[97m"
C_GRAY = "\033[90m"
BOLD = "\033[1m"
DIM = "\033[2m"


def _enable_windows_vt():
    """Windows 10+ 控制台开启 VT 转义支持（ANSI 颜色 / 清屏依赖它）。"""
    global USE_VT
    if os.name != "nt":
        USE_VT = True
        return
    try:
        import ctypes
        k = ctypes.windll.kernel32
        ok = False
        for handle_id in (-11, -12):        # stdout / stderr
            h = k.GetStdHandle(handle_id)
            mode = ctypes.c_uint32()
            if k.GetConsoleMode(h, ctypes.byref(mode)):
                k.SetConsoleMode(h, mode.value | 0x0004)
                ok = True
        USE_VT = ok
    except Exception:
        USE_VT = False


def clear_screen():
    """清屏，用于功能界面切换。

    仅在真实终端且支持 ANSI 转义时执行；重定向到日志、旧版控制台等环境自动跳过，
    避免把控制字符写进日志文件。
    """
    if not USE_VT or not sys.stdout.isatty():
        return
    sys.stdout.write("\033[2J\033[H")
    sys.stdout.flush()


def init_colors(force_off=False):
    """决定是否启用彩色：重定向/管道、NO_COLOR、--no-color 时自动回退纯文本。"""
    global USE_COLOR
    _enable_windows_vt()
    USE_COLOR = ((not force_off)
                 and os.environ.get("NO_COLOR") is None
                 and sys.stdout.isatty())
    return USE_COLOR


def clr(text, *codes):
    """给文本套色；未启用颜色时原样返回，保证纯文本环境不乱码。"""
    if not USE_COLOR or not codes:
        return str(text)
    return "".join(codes) + str(text) + _RESET


def _strip_ansi(s):
    return re.sub(r"\033\[[0-9;]*m", "", s or "")


def _box(lines, width=BOX_W):
    """画一个彩色圆角框；行内可含 ANSI 颜色，按可视宽度自动对齐。"""
    top = "╭" + "─" * (width - 2) + "╮"
    bot = "╰" + "─" * (width - 2) + "╯"
    out = [clr(top, C_CYAN)]
    for ln in lines:
        vis_w = _disp_width(_strip_ansi(ln))
        out.append(clr("│", C_CYAN) + " " + ln
                   + " " * max(0, width - 3 - vis_w) + clr("│", C_CYAN))
    out.append(clr(bot, C_CYAN))
    return "\n".join(out)


def _title(text, mark=C_CYAN):
    """分区标题：左侧竖条 + 加粗标题，便于新手快速定位当前步骤。"""
    return clr("▌", mark) + " " + clr(text, BOLD)


def _step(n, total, text):
    """步骤标记，如 [2/4] 获取课程列表。"""
    return clr("[%d/%d]" % (n, total), C_MAGENTA, BOLD) + " " + clr(text, BOLD, C_CYAN)


def _hint(text):
    """黄色提示行（给新手的下一步建议）。"""
    return clr("提示：", C_YELLOW, BOLD) + clr(text, C_YELLOW)


# ============================== 日志 / 错误收集 ==============================

LOG_PATH = None          # 日志文件路径
ERRORS = []              # 已收集的错误清单：[{context, error, traceback}, ...]
_IO_LOCK = threading.RLock()   # 多线程上报时保护日志写入与控制台输出（可重入）


def init_logging():
    """选择可写的日志路径并清空。"""
    global LOG_PATH
    candidates = []
    try:
        candidates.append(os.path.dirname(os.path.abspath(sys.argv[0])))
    except Exception:
        pass
    candidates.append(os.getcwd())
    try:
        candidates.append(tempfile.gettempdir())
    except Exception:
        pass
    LOG_PATH = "polymas_auto.log"
    for d in candidates:
        try:
            p = os.path.join(d, "polymas_auto.log")
            with open(p, "w", encoding="utf-8") as f:
                f.write("Polymas 自动看课日志  启动于 %s\n" % time.strftime("%Y-%m-%d %H:%M:%S"))
            LOG_PATH = p
            break
        except Exception:
            continue
    return LOG_PATH


def write_log(msg, level="INFO"):
    """把一行带时间戳的内容追加进日志文件（多线程下加锁，避免行错乱）。"""
    line = "%s [%s] %s" % (time.strftime("%Y-%m-%d %H:%M:%S"), level, msg)
    if LOG_PATH:
        try:
            with _IO_LOCK:
                with open(LOG_PATH, "a", encoding="utf-8") as f:
                    f.write(line + "\n")
        except Exception:
            pass


def record_error(context, exc):
    """记录一个错误：打印到控制台 + 写入日志(含堆栈) + 加入错误清单。"""
    tb = traceback.format_exc()
    if "NoneType: None" in tb:
        tb = ""
    with _IO_LOCK:
        ERRORS.append({"context": context, "error": str(exc), "traceback": tb})
        write_log("错误 @ %s: %s\n%s" % (context, exc, tb), level="ERROR")
        print("  " + clr("✗ [错误]", C_RED, BOLD) + " "
              + clr(context, C_YELLOW) + "：" + clr(exc, C_RED))


def error_summary():
    """打印错误汇总。"""
    if not ERRORS:
        print("\n  " + clr("✓ [状态]", C_GREEN, BOLD) + " " + clr("本次未发生错误。", C_GREEN))
        return
    print("\n" + clr("=" * 58, C_RED))
    print("  " + clr("错误汇总（共 %d 个）" % len(ERRORS), C_RED, BOLD))
    print(clr("=" * 58, C_RED))
    for i, e in enumerate(ERRORS, 1):
        print("  " + clr("%d)" % i, C_RED, BOLD) + " "
              + clr(e["context"], C_YELLOW) + "：" + e["error"])
    print("  " + clr("详细堆栈见日志文件：%s" % LOG_PATH, C_GRAY))


# ============================== 常量 ==============================

# 学校仅作为“询问时的默认值”，账号密码不再内置，启动时询问
DEFAULT_SCHOOL = "南京邮电大学"

# 南邮登录页固定的 AES 密钥后缀（key = iv = "iam" + 该值）
NJ_CHECK_KEY = "1629428467008"

# 目标课程页（登录成功后要落地的 redirect 目标，同时也作为默认看课对象）
HOST_URL = ("https://hike-teaching-center.polymas.com/"
            "agent-course-full/4ba83RJ8OETYLjK9Adz6/stu/study")

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36")

API_BASE = "https://cloudapi.polymas.com"
P_IDENTITY = "/oauth/token/getIdentity"
P_COURSES = "/student-course/student/index/queryStudentCourse"
P_LIBRARY = "/teacher-course/library/course/findStudyLibraryByCourseId"
P_TREE = "/student-course/study/student/resource/queryTree"
P_REPORT = "/student-course/study/student/record/report"

CLIENT_TYPE = "Windows"

# 上报节奏参数（让观看时间线看起来像真实播放，而不是"一次跳满"）
CHUNK_SEC = 60          # 默认分片步长：每片上报一次进度（秒）
CHUNK_JITTER = 0.25     # 分片长度抖动比例（±25%）
CHUNK_DELAY = (0.05, 0.15)   # 相邻分片之间的真实等待区间（秒）
VIDEO_DELAY = (0.2, 0.2)     # 两段视频之间的真实等待（秒，固定 0.2，仅单线程时生效）

# 并发上报：每个视频一个线程，支持 1~32 线程
THREADS_MAX = 32
THREADS_DEFAULT = 8


# ============================== 登录（纯 HTTP SSO） ==============================

def _aes_encrypt(plain, key_str):
    """南邮登录加密：AES-CBC(key=iv=('iam'+key_str))，PKCS7 填充，输出 hex。"""
    key = ("iam" + key_str).encode("utf-8")
    padlen = 16 - (len(plain.encode("utf-8")) % 16)
    data = plain.encode("utf-8") + bytes([padlen]) * padlen
    c = Cipher(algorithms.AES(key), modes.CBC(key)).encryptor()
    return (c.update(data) + c.finalize()).hex()


def _cookies(s):
    return {c.name: c.value for c in s.cookies}


def _sso_login_once(user, password, school, log):
    """单次 SSO 登录尝试，成功返回 (token, session)，未拿到 token 返回 (None, session)。"""
    s = requests.Session()
    s.headers.update({"User-Agent": UA})

    # 1) 取学校 SSO loginUrl
    r = s.get("https://user.zhihuishu.com/zhsuser/accountV2/findSchoolV2",
              params={"page": 1, "pageSize": 9999}, timeout=20)
    login_url = None
    for it in (r.json().get("rt") or []):
        if it.get("name") == school:
            login_url = it.get("loginUrl")
            break
    if not login_url:
        raise RuntimeError("未找到学校：%s" % school)
    log("[1] 学校 SSO:", login_url)

    # 2) 打开 njuptsso，落到南邮认证页，拿到 CAS service(JSESSIONID)
    r = s.get(login_url, allow_redirects=True, timeout=20)
    log("[2] 认证页:", r.url, r.status_code)

    # 3) 提交账号密码（AES 加密）
    payload = {
        "checkKey": NJ_CHECK_KEY,
        "username": _aes_encrypt(user, NJ_CHECK_KEY),
        "password": _aes_encrypt(password, NJ_CHECK_KEY),
        "mode": "none",
    }
    r = s.post("https://i.njupt.edu.cn/ssoLogin/login", json=payload,
               headers={"Content-Type": "application/json",
                        "X-Requested-With": "XMLHttpRequest",
                        "Referer": r.url, "Origin": "https://i.njupt.edu.cn"},
               timeout=20)
    j = r.json()
    if not j.get("success"):
        raise RuntimeError("南邮登录失败：%s" % j.get("message"))
    log("[3] 南邮登录成功：%s" % (j.get("result", {}).get("userInfo", {}).get("realname")))

    # 4) 拿 CAS ticket，落到 login.zhihuishu.com/wxTransit?cacheId=xxx
    r = s.get("https://i.njupt.edu.cn/cas/login", params={"service": login_url},
              allow_redirects=True, timeout=20)
    cache_id = (parse_qs(urlparse(r.url).query).get("cacheId") or [""])[0]
    if not cache_id:
        raise RuntimeError("未拿到 cacheId，落点：%s" % r.url)
    log("[4] 中转 cacheId:", cache_id)

    # 5) 取一次性密码
    pwd = None
    for name, url in [
        ("skipSet", "https://user.zhihuishu.com/zhsuser/login/code/skipSet/" + cache_id),
        ("useCurrentAccount", "https://user.zhihuishu.com/zhsuser/login/useCurrentAccount/" + cache_id),
    ]:
        rr = s.post(url, headers={"Content-Type": "application/json;charset=UTF-8"}, timeout=20)
        try:
            jj = rr.json()
            if jj.get("status") == 1 and jj.get("rt", {}).get("pwd"):
                pwd = jj["rt"]["pwd"]
                break
        except Exception:
            pass
    if not pwd:
        raise RuntimeError("未拿到一次性密码")
    log("[5] 一次性密码 ok")

    # 6) passport 换 ticket -> cloudapi ssoLogin -> 下发 ai-poly
    #    注意：service 必须原样拼进 URL，不能交给 requests.params 再编码一次
    inner = quote(HOST_URL, safe="")
    cloud_inner = API_BASE + "/oauth/login/ssoLogin?redirect=" + inner
    service = quote(cloud_inner, safe="")
    url = "https://passport.zhihuishu.com/login?pwd=%s&service=%s" % (pwd, service)
    r = s.get(url, allow_redirects=True, timeout=20)
    token = _cookies(s).get("ai-poly")
    if not token:
        log("[6] 未拿到 ai-poly，末次落点:", r.url, r.status_code)
        return None, s
    log("[6] 获取 ai-poly ok")
    return token, s


def sso_login(user, password, school=DEFAULT_SCHOOL, verbose=True, retries=5):
    """
    纯 HTTP 完成 SSO 登录，返回 ai-poly token（内部自动重试，链路偶尔会抖动）。
    链路：南邮CAS(账号密码) -> njuptsso -> login.zhihuishu.com/wxTransit
          -> 一次性密码 -> passport -> cloudapi ssoLogin(ticket) -> ai-poly
    """
    def log(*a):
        if verbose:
            print(*a, flush=True)

    last_err = None
    for i in range(1, retries + 1):
        if i > 1:
            log("[*] 重试登录（第 %d 次）..." % i)
        try:
            token, _ = _sso_login_once(user, password, school, log)
            if token:
                return token
            last_err = RuntimeError("未拿到 ai-poly cookie")
        except Exception as e:
            last_err = e
            log("[*] 登录失败：%s" % e)
            if "用户名或密码错误" in str(e):
                break        # 账号密码错误，重试无意义
        time.sleep(1.5)
    raise RuntimeError("SSO 登录重试 %d 次仍失败：%s" % (retries, last_err))


# ============================== 课程接口 ==============================

def _request(headers_of, path, method="GET", body=None, params=None, timeout=30):
    """headers_of: 由 token 生成请求头的回调。"""
    url = API_BASE + path
    if params:
        from urllib.parse import urlencode
        url += "?" + urlencode(params)
    data = None
    if body is not None:
        data = json.dumps(body, ensure_ascii=False).encode("utf-8")
        method = "POST"
    resp = requests.request(method, url, data=data, headers=headers_of(), timeout=timeout)
    try:
        return resp.json()
    except Exception:
        raise RuntimeError("HTTP %s: %s" % (resp.status_code, resp.text[:300]))


def _check(j):
    if j.get("code") != 200:
        raise RuntimeError("接口异常: code=%s msg=%s" % (j.get("code"), j.get("msg")))
    return j.get("data")


class Polymas:
    """封装 cloudapi 请求（鉴权用 ai-poly，兼容 Authorization 与 Cookie 两种校验）。"""

    def __init__(self, token):
        self.token = token

    def _headers(self):
        return {
            "Content-Type": "application/json; charset=utf-8",
            "Accept": "application/json, text/plain, */*",
            "Authorization": self.token,
            "Cookie": "ai-poly=%s" % self.token,
            "User-Agent": UA,
        }

    def _get(self, path, params=None):
        return _check(_request(self._headers, path, params=params))

    def _post(self, path, body=None):
        return _check(_request(self._headers, path, body=body if body is not None else {}))

    def me(self):
        return self._get(P_IDENTITY)

    def courses(self):
        data = self._post(P_COURSES, {})
        return data.get("list", []) if isinstance(data, dict) else (data or [])

    def library_folder(self, course_id, term):
        data = self._get(P_LIBRARY, params={"courseId": course_id, "term": term})
        write_log("资源库接口返回 type=%s data=%r" % (type(data).__name__, data))
        if not data:
            raise RuntimeError("未取到资源库 libraryFolderId")
        # 正常情况 data 就是文件夹 ID 字符串；个别课程（专题课等）会包一层对象/数组，
        # 这里统一取出真正的 folderId，避免把整个对象当成 ID 发出去
        if isinstance(data, str):
            return data
        if isinstance(data, dict):
            for k in ("libraryFolderId", "folderId", "id", "libraryId"):
                if data.get(k):
                    return data[k]
        if isinstance(data, list) and data:
            first = data[0]
            if isinstance(first, dict):
                for k in ("libraryFolderId", "folderId", "id", "libraryId"):
                    if first.get(k):
                        return first[k]
            elif isinstance(first, str):
                return first
        return str(data)

    def tree(self, course_id, term, library_folder_id, class_id=None):
        body = {
            "libraryFolderId": library_folder_id,
            "courseId": course_id,
            "term": term,
        }
        if class_id:
            body["classId"] = class_id
        write_log("queryTree 请求体: %s" % json.dumps(body, ensure_ascii=False))
        data = self._post(P_TREE, body)
        items = []

        def walk(nodes):
            for node in (nodes or []):
                detail = node.get("detail") or {}
                children = node.get("children") or []
                if not children:
                    ext = {}
                    if detail.get("ext"):
                        try:
                            ext = json.loads(detail["ext"])
                        except Exception:
                            ext = {}
                    if node.get("nodeId") and (detail.get("classify") == "file" or ext.get("duration")):
                        items.append({
                            "nodeId": node.get("nodeId"),
                            "title": detail.get("title"),
                            "duration": ext.get("duration") or 0,
                            "isFinished": bool(node.get("isFinished")),
                            "pct": node.get("completePercentage"),
                        })
                else:
                    walk(children)

        walk(data)
        return items

    def report(self, course_id, term, resource_id, start_sec, end_sec,
               study_total, start_date, end_date):
        """上报一个观看分片。

        startWatchTime / endWatchTime 是本次分片在视频里的起止秒数，
        studyTotalTime 是该视频累计已看秒数（= endWatchTime）；
        startDate / endDate 与这一段增量严格对应，
        保证"时间戳差值 == 本次观看时长"，不会出现 1 秒读完 900 秒的矛盾。
        """
        data = self._post(P_REPORT, {
            "startWatchTime": int(start_sec),
            "endWatchTime": int(end_sec),
            "startDate": start_date,
            "endDate": end_date,
            "studyTotalTime": int(study_total),
            "courseId": course_id,
            "resourceId": resource_id,
            "clientType": CLIENT_TYPE,
            "term": term,
        })
        return (data or {}).get("completeRate")


# ============================== 选课 / 看课 ==============================

def pick_course(courses, selector):
    if not courses:
        raise RuntimeError("账号下没有课程")
    s = str(selector).strip()
    if s.isdigit():
        idx = int(s)
        if not (1 <= idx <= len(courses)):
            raise RuntimeError("序号超范围：1~%d" % len(courses))
        return courses[idx - 1]
    for c in courses:
        if c.get("courseId") == s:
            return c
    hits = [c for c in courses if s in (c.get("courseName") or "")]
    if len(hits) == 1:
        return hits[0]
    if len(hits) > 1:
        raise RuntimeError("名称匹配多门课，请用序号/courseId：%s"
                           % ", ".join(c.get("courseName", "") for c in hits))
    raise RuntimeError("未匹配到课程：%s" % s)


def get_term(course, term_arg=None):
    if term_arg:
        return int(term_arg)
    terms = course.get("terms") or []
    if not terms:
        raise RuntimeError("课程没有可用学期")
    return int(terms[0])


def get_class_id(course):
    """取课程的班级 ID（queryTree 需要它，否则接口会报"参数不能为空"）。

    queryStudentCourse 返回的课程里，班级 ID 可能在顶层 classId，
    也可能在 studentClasses[] 里（一个课程可能属于多个班）。
    """
    cid = course.get("classId")
    if cid:
        return cid
    for clazz in (course.get("studentClasses") or []):
        if isinstance(clazz, dict) and clazz.get("classId"):
            return clazz["classId"]
        if isinstance(clazz, str) and clazz:
            return clazz
    return None


def print_courses(courses):
    """打印课程列表（序号便于后续选择）。"""
    print("\n" + clr(LINE, C_BLUE))
    print("  " + _title("可看课程") + "  " + clr("共 %d 门" % len(courses), C_GRAY))
    print(clr(LINE, C_BLUE))
    name_w = min(40, max([_disp_width(c.get("courseName") or "") for c in courses] + [8]))
    for i, c in enumerate(courses, 1):
        terms = "/".join(str(t) for t in (c.get("terms") or []))
        print("  " + clr("%2d)" % i, C_YELLOW, BOLD) + " "
              + _pad(c.get("courseName") or "", name_w)
              + "  " + clr("学期 %s" % terms, C_GRAY))
    print(clr(LINE, C_BLUE))


def _toggle_realtime(opts):
    """切换上报节奏（压缩发送 <-> 真实时间间隔），并打印切换结果。返回切换后的值。"""
    opts["realtime"] = not opts.get("realtime")
    if opts["realtime"]:
        print("  " + clr("已切换为「真实时间间隔」", C_GREEN, BOLD)
              + clr("：请求会按实际观看时长逐条发出，整批耗时 ≈ 全部视频总时长，", C_YELLOW))
        print("  " + _hint("可能长达数小时，请确保电脑不会休眠或断网；"
                           "再输入一次 r / safe 可改回压缩发送。"))
    else:
        print("  " + clr("已切换为「压缩发送」", C_YELLOW, BOLD)
              + clr("：按分片快速上报，请求到达时间会早于上报的观看时间。", C_GRAY))
    return opts["realtime"]


def choose_courses(courses, opts=None):
    """交互式选择要看的课程。支持多选(1,3)、0=全部、r/safe=切换上报节奏、q=退出。

    opts 为可变的设置字典（含 realtime / threads），界面里输入 r / safe 就地切换，
    调用方读同一个字典即可拿到用户的选择。
    """
    if not courses:
        return []
    if opts is None:
        opts = {}
    opts.setdefault("realtime", False)
    while True:
        print("\n" + clr(LINE, C_BLUE))
        print("  " + _title("请选择要看的课程"))
        print(clr(LINE, C_BLUE))
        name_w = min(40, max([_disp_width(c.get("courseName") or "") for c in courses] + [8]))
        for i, c in enumerate(courses, 1):
            terms = "/".join(str(t) for t in (c.get("terms") or []))
            print("  " + clr("%2d)" % i, C_YELLOW, BOLD) + " "
                  + _pad(c.get("courseName") or "", name_w)
                  + "  " + clr("学期 %s" % terms, C_GRAY))
        print("  " + clr("%2d)" % 0, C_GREEN, BOLD) + " " + clr("全部课程", C_GREEN))
        print(clr(LINE, C_BLUE))
        # 上报设置（按 r 切换，可随时改）
        if opts.get("realtime"):
            print("  " + clr("r)", C_GREEN, BOLD) + " " + clr("上报节奏：", C_GRAY)
                  + clr("真实时间间隔", C_GREEN, BOLD)
                  + clr("  请求到达时间 ≈ 上报的观看时间", C_GRAY))
            print("       " + clr("整批耗时 ≈ 全部视频总时长，很慢；选课后立即生效", C_YELLOW))
        else:
            print("  " + clr("r)", C_YELLOW, BOLD) + " " + clr("上报节奏：", C_GRAY)
                  + clr("压缩发送", C_YELLOW, BOLD)
                  + clr("  请求到达时间早于上报的观看时间", C_GRAY))
            print("       " + clr("很快；想更贴近真实观看可输入 r / safe 切换", C_GRAY))
        print(clr(LINE, C_BLUE))
        print("  " + clr("输入示例：  1  或  1,3  选课程      0  全部      "
                         "r / safe  切换上报节奏      q  退出", C_GRAY))
        try:
            raw = input(clr("请输入序号 > ", C_CYAN, BOLD))
        except (EOFError, KeyboardInterrupt):
            print()
            return []
        # 输入法常把 r 打成全角 ｒ、把逗号打成 ，：统一转半角小写后再解析，
        # 否则"序号里混入 r"会被当成非法序号
        raw = "".join(_to_ascii_char(ch) for ch in raw).strip().lower()
        if raw in ("q", "quit", "exit"):
            return []
        parts = [p for p in re.split(r"[,\s]+", raw) if p]
        # r / safe 出现在输入里（单独写、或与序号连着写如 1r）就切换上报节奏；
        # 去掉这些字母后，剩下的数字照常按序号处理
        if any(w in ("r", "safe") for w in re.findall(r"[a-z]+", raw)):
            _toggle_realtime(opts)
            raw = re.sub(r"safe|r", " ", raw)
            parts = [p for p in re.split(r"[,\s]+", raw) if p]
            if not parts:
                continue
        if not parts:
            print("  " + clr("! 输入为空，请重新输入", C_YELLOW))
            continue
        if len(parts) == 1 and parts[0] in ("0", "all", "*"):
            return list(courses)
        bad = [p for p in parts if not p.isdigit() or not (1 <= int(p) <= len(courses))]
        if bad:
            print("  " + clr("! 无效序号：%s，请重新输入" % ", ".join(bad), C_YELLOW))
            continue
        return [courses[i - 1] for i in sorted({int(p) for p in parts})]


def _progress_bar(cur, total, width=28):
    pct = (cur / total) if total else 1.0
    filled = int(round(width * pct))
    bar = (clr("█" * filled, C_GREEN, BOLD)
           + clr("░" * (width - filled), C_GRAY))
    return "[%s] %s/%s (%s)" % (bar, clr(cur, C_CYAN, BOLD), total,
                                clr("%d%%" % int(pct * 100), C_YELLOW, BOLD))


def _short(title, n=34):
    title = title or ""
    return title if len(title) <= n else title[:n - 1] + "…"


def _disp_width(s):
    """按终端显示宽度计算（中文按 2 列）。"""
    return sum(2 if unicodedata.east_asian_width(ch) in ("W", "F") else 1 for ch in s)


def _trunc(s, width):
    """按显示宽度截断字符串。"""
    out, w = [], 0
    for ch in s or "":
        cw = 2 if unicodedata.east_asian_width(ch) in ("W", "F") else 1
        if w + cw > width:
            break
        out.append(ch)
        w += cw
    return "".join(out)


def _pad(s, width):
    """按显示宽度右侧补空格对齐。"""
    s = _trunc(s, width)
    return s + " " * max(0, width - _disp_width(s))


def _chunk_plan(duration, step):
    """把一个视频的时长切成若干观看分片，返回 [(start_sec, end_sec), ...]。

    分片长度带 ±25% 抖动，避免每片长度都一模一样这种机器特征。
    """
    duration = max(1, int(duration or 0))
    if step <= 0 or duration <= step:
        return [(0, duration)]
    plan, pos = [], 0
    while pos < duration:
        seg = max(5, int(step * random.uniform(1 - CHUNK_JITTER, 1 + CHUNK_JITTER)))
        nxt = min(duration, pos + seg)
        plan.append((pos, nxt))
        pos = nxt
    return plan


def brush_course(poly, course, term_arg=None, force=False, dry_run=False,
                 tty=None, chunk=CHUNK_SEC, threads=THREADS_DEFAULT, realtime=False):
    """看一门课：拿到资源树，按分片逐步上报到 100%，过程中显示进度。返回统计。"""
    course_id = course.get("courseId")
    name = course.get("courseName")
    term = get_term(course, term_arg)
    class_id = get_class_id(course)
    if tty is None:
        tty = sys.stdout.isatty()
    print("\n" + clr("═" * 58, C_MAGENTA))
    print("  " + clr("课程：", C_GRAY) + clr(name, BOLD, C_WHITE)
          + "    " + clr("学期 %s" % term, C_GRAY))
    print(clr("═" * 58, C_MAGENTA))

    write_log("课程字段 courseId=%r classId=%r term=%r" % (course_id, class_id, term))
    folder_id = poly.library_folder(course_id, term)
    items = poly.tree(course_id, term, folder_id, class_id)
    if not items:
        print("  " + clr("该课程下暂无可看视频，已跳过。", C_YELLOW))
        return {"total": 0, "done": 0}

    todo = [it for it in items if force or not it["isFinished"]]
    print("  共 %s 个视频，其中待看 %s 个"
          % (clr(len(items), C_CYAN, BOLD), clr(len(todo), C_YELLOW, BOLD)))
    # 线程数：每个视频一个线程，1~32
    workers = max(1, min(THREADS_MAX, int(threads or 1), len(todo) or 1))
    print("  " + clr("并发线程：", C_GRAY) + clr(workers, C_CYAN, BOLD)
          + clr("（每个视频一个线程，各视频同步上报）", C_GRAY))
    # 上报节奏：--realtime 时按真实时间等待，请求到达时间与上报时间一致
    if realtime:
        print("  " + clr("上报节奏：", C_GRAY) + clr("按真实时间间隔发送", C_GREEN, BOLD)
              + clr("（整批耗时 ≈ 总时长，最贴近真实观看，但很慢）", C_GRAY))
    else:
        print("  " + clr("上报节奏：", C_GRAY) + clr("分片压缩发送", C_YELLOW, BOLD)
              + clr("（很快，但请求到达时间早于上报的观看时间）", C_GRAY))
    write_log("课程 %s(%s) 学期=%s：共 %d 个视频，待看 %d 个，线程数 %d，节奏=%s"
              % (name, course_id, term, len(items), len(todo), workers,
                 "真实时间" if realtime else "压缩"))

    if dry_run:
        for i, it in enumerate(todo, 1):
            print("  " + clr("[预览]", C_BLUE, BOLD) + " (%d/%d) %s  时长=%ss  拟分 %d 片  当前=%s%%"
                  % (i, len(todo), it["title"], it["duration"],
                     len(_chunk_plan(it["duration"], chunk)), it["pct"]))
        print("  " + _hint("这是 --dry-run 试运行模式，只查看、不会真的上报。"))
        return {"total": len(items), "done": sum(1 for it in items if it["isFinished"])}

    # —— 观看时间线 ——
    # 默认（压缩）模式：把整批视频串成一条连续时间线，最后一片的结束时间贴近真实当前时间，
    # 这样每个视频的起止时间不重叠、不与真实时间脱节，看起来就是一路看下来的。
    # 多线程并发只改变"请求什么时候发出"，时间线本身仍按顺序排布，保持自洽。
    # --realtime 模式：不再预排时间线，每个视频以自己真实开始的时刻为锚点，
    # 并按真实时长等待后再发下一片，于是"请求到达时间"与"上报的观看时间"基本重合。
    timeline_start = None
    v_starts = {}
    if not realtime:
        total_secs = sum(max(1, int(it["duration"] or 0)) for it in todo) or 1
        timeline_start = time.time() - total_secs - random.uniform(0.5, 3.0)
        cursor = 0.0
        for it in todo:
            v_starts[it["nodeId"]] = cursor
            cursor += max(1, int(it["duration"] or 0))

    fail_count = [0]
    done_count = [0]

    def watch_one(it):
        """单个视频：分片依次上报（同一视频内部仍严格顺序推进），返回 (plan, rate)。"""
        plan = _chunk_plan(it["duration"], chunk)
        # 锚点：真实模式取本线程开始处理的时刻；压缩模式取预排时间线上的位置
        anchor = time.time() if realtime else timeline_start + v_starts[it["nodeId"]]
        rate = None
        for idx, (cs, ce) in enumerate(plan):
            if realtime:
                # 等到这一片真的"看完"再上报，使请求到达时间 ≈ 上报的结束时间
                left = (anchor + ce) - time.time()
                if left > 0:
                    time.sleep(left)
            sdt = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(anchor + cs))
            edt = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(anchor + ce))
            rate = poly.report(course_id, term, it["nodeId"], cs, ce, ce, sdt, edt)
            write_log("分片上报 %s  %s~%ss  %s -> %s  completeRate=%s"
                      % (it["title"], cs, ce, sdt, edt, rate))
            if not realtime and idx < len(plan) - 1:
                time.sleep(random.uniform(*CHUNK_DELAY))
        return plan, rate

    with ThreadPoolExecutor(max_workers=workers) as ex:
        futures = {ex.submit(watch_one, it): it for it in todo}
        for fut in as_completed(futures):
            it = futures[fut]
            try:
                plan, rate = fut.result()
            except Exception as e:
                fail_count[0] += 1
                with _IO_LOCK:
                    if tty:
                        sys.stdout.write("\r" + " " * 78 + "\r")
                        sys.stdout.flush()
                    record_error("上报视频 %s" % it["title"], e)
                write_log("上报参数 course=%s term=%s resource=%s duration=%s"
                          % (course_id, term, it["nodeId"], it["duration"]))
                continue
            done_count[0] += 1
            i = done_count[0]
            with _IO_LOCK:
                if tty:
                    sys.stdout.write("\r  " + _progress_bar(i, len(todo)) + "  "
                                     + clr(_short(it["title"]), C_GRAY) + "   ")
                    sys.stdout.flush()
                else:
                    print("  " + clr("✓", C_GREEN, BOLD)
                          + " [%d/%d] (%d%%) %s -> completeRate=%s"
                          % (i, len(todo), int(i / len(todo) * 100), it["title"], rate))
            write_log("上报成功 [%d/%d] %s -> completeRate=%s（分 %d 片）"
                      % (i, len(todo), it["title"], rate, len(plan)))
            # 视频间等待只在单线程时才有意义（多线程下各视频本就并行）
            if workers == 1:
                time.sleep(random.uniform(*VIDEO_DELAY))
    fail_count = fail_count[0]
    if tty and todo:
        sys.stdout.write("\n")
        sys.stdout.flush()

    # 复核
    final = poly.tree(course_id, term, folder_id, class_id)
    done = sum(1 for it in final if it["isFinished"])
    print("\n  " + _step(4, 4, "复核结果"))
    print("  " + clr("✓ [完成]", C_GREEN, BOLD) + " 复核：%s/%s 个视频已完成"
          % (clr(done, C_GREEN, BOLD), len(final)))
    if done == len(final):
        print("  " + _hint("这门课已全部看完，可以返回去选择其它课程。"))
    if fail_count:
        print("  " + clr("⚠ [提示]", C_YELLOW, BOLD) + " "
              + clr("本次有 %d 个视频上传失败，详见上方错误与日志文件" % fail_count, C_YELLOW))
        print("  " + _hint("重新运行并加 --force 参数可以重试未完成的视频。"))
    write_log("课程 %s 复核：%d/%d 已完成，失败 %d 个"
              % (name, done, len(final), fail_count))
    return {"total": len(final), "done": done}


# ============================== 入口 ==============================

def _pause(prompt):
    """暂停等待用户输入。返回 True=继续，False=退出。非终端环境直接返回 False。"""
    if not sys.stdin.isatty():
        return False
    try:
        ans = input(prompt).strip().lower()
    except (EOFError, KeyboardInterrupt):
        return False
    return ans not in ("q", "quit", "exit")


def _read_any_key():
    """读取单个按键，不需要回车。Windows 用 msvcrt，其它平台用 tty 原始模式。

    返回按键字符；读取失败（不支持的环境）返回 None。
    """
    try:
        if os.name == "nt":
            import msvcrt
            ch = msvcrt.getch()
            return ch.decode("utf-8", "ignore") if isinstance(ch, bytes) else ch
        import termios
        import tty
        fd = sys.stdin.fileno()
        old = termios.tcgetattr(fd)
        try:
            # TCSADRAIN：保留用户已经按下的键，不用 TCSAFLUSH 丢掉
            tty.setraw(fd, when=termios.TCSADRAIN)
            return sys.stdin.read(1)
        finally:
            termios.tcsetattr(fd, termios.TCSADRAIN, old)
    except Exception:
        return None


def confirm_disclaimer():
    """首页免责声明确认：按下任意键表示已阅读并同意。

    返回 True=同意继续，False=不同意（用户按 q / Esc / Ctrl+C）而退出。
    非交互环境（重定向、CI）无法按键，视为已同意并写入日志。
    """
    print()
    print("  " + clr("━" * 58, C_RED))
    print("  " + clr("⚠ 免责声明（务必阅读）", BOLD, C_RED))
    print("  " + clr("━" * 58, C_RED))
    for ln in (
        "本工具仅供个人学习、接口研究与技术交流，请勿用于任何商业用途。",
        "严禁使用本工具从事代刷课、代看收费、买卖学分等牟利行为！",
        "由此造成的账号封禁、成绩作废、纪律处分等后果全部由使用者自负，作者不承担任何责任。",
        "本程序不保存账号密码，也不会上传任何个人信息到第三方。",
        "请遵守所在学校的规定与相关法律法规，以正常学习为主。",
    ):
        print("   " + clr("· ", C_RED) + clr(ln, C_WHITE))
    print("  " + clr("━" * 58, C_RED))
    print("  " + clr("按下任意键即表示你已阅读并同意上述声明", BOLD, C_RED)
          + clr("（按 q / Esc 表示不同意并退出）", C_GRAY))
    if not sys.stdin.isatty():
        print("  " + _hint("当前为非交互环境，无法按键，视为已同意上述声明。"))
        write_log("非交互环境：跳过免责声明确认（视为已同意）")
        return True
    key = _read_any_key()
    if key is None:
        write_log("无法读取按键：免责声明视为已同意")
        return True
    print()
    if key in ("q", "Q", "\x1b", "\x03"):
        print("  " + clr("✗ 你未同意上述声明，已退出。", C_RED, BOLD))
        write_log("用户不同意免责声明，退出")
        return False
    print("  " + clr("✓ 已确认同意免责声明，继续。", C_GREEN, BOLD))
    write_log("用户已确认同意免责声明")
    return True


# 全角/中文标点 -> ASCII 的补充映射（NFKC 处理不到的少数字符）
_TO_ASCII_EXTRA = {
    "。": ".", "、": ",", "：": ":", "；": ";", "（": "(", "）": ")",
    "【": "[", "】": "]", "《": "<", "》": ">",
    "！": "!", "？": "?", "“": '"', "”": '"', "‘": "'", "’": "'",
    "～": "~", "－": "-", "／": "/", "＼": "\\", "｜": "|", "　": " ",
}


def _to_ascii_char(ch):
    """把中文/全角字符转成对应的英文字符（如 Ｈ->H, １->1, 。->.）。"""
    if ch in _TO_ASCII_EXTRA:
        return _TO_ASCII_EXTRA[ch]
    return unicodedata.normalize("NFKC", ch)


def _read_password(prompt="密码："):
    """逐字符读取密码：回显星号、支持退格、全角自动转半角。"""
    sys.stdout.write(prompt)
    sys.stdout.flush()
    buf = []
    try:
        import msvcrt  # Windows 控制台
        while True:
            ch = msvcrt.getwch()
            if ch in ("\r", "\n"):
                break
            if ch == "\x03":                       # Ctrl+C
                raise KeyboardInterrupt
            if ch in ("\x00", "\xe0"):             # 功能键/方向键前缀，跳过
                msvcrt.getwch()
                continue
            if ch in ("\x08", "\x7f"):             # 退格
                if buf:
                    buf.pop()
                    sys.stdout.write("\b \b")
                    sys.stdout.flush()
                continue
            ch = _to_ascii_char(ch)
            if not ch.isprintable():
                continue
            buf.append(ch)
            sys.stdout.write("*" * len(ch))
            sys.stdout.flush()
    except ImportError:
        buf = _read_password_unix()
    sys.stdout.write("\n")
    sys.stdout.flush()
    return "".join(buf)


def _read_password_unix():
    """类 Unix 终端的逐字符密码输入（回显星号、退格、全角转半角）。"""
    import termios
    import tty
    fd = sys.stdin.fileno()
    old = termios.tcgetattr(fd)
    buf = []

    def read_char():
        b = os.read(fd, 1)
        if not b:
            return ""
        n = b[0]
        need = 0
        if n & 0x80 == 0:
            need = 0
        elif n & 0xE0 == 0xC0:
            need = 1
        elif n & 0xF0 == 0xE0:
            need = 2
        elif n & 0xF8 == 0xF0:
            need = 3
        data = b
        for _ in range(need):
            data += os.read(fd, 1)
        return data.decode("utf-8", "replace")

    try:
        tty.setraw(fd)
        while True:
            ch = read_char()
            if ch == "":
                break
            if ch in ("\r", "\n"):
                break
            if ch == "\x03":
                raise KeyboardInterrupt
            if ch in ("\x08", "\x7f"):
                if buf:
                    buf.pop()
                    sys.stdout.write("\b \b")
                    sys.stdout.flush()
                continue
            ch = _to_ascii_char(ch)
            if not ch.isprintable():
                continue
            buf.append(ch)
            sys.stdout.write("*" * len(ch))
            sys.stdout.flush()
    finally:
        termios.tcsetattr(fd, termios.TCSADRAIN, old)
    return buf


def _ask_password():
    """密码输入：回显星号，全角自动转半角。"""
    return _read_password("密码：")


def collect_login(args):
    """收集登录信息：优先 --user/--pass（或环境变量），否则启动时交互询问。"""
    user = args.user
    password = args.password
    if not user or not password:
        if not sys.stdin.isatty():
            raise RuntimeError("非交互环境必须提供账号密码：--user/--pass 或环境变量 ZHS_USER/ZHS_PASS")
        print("\n" + clr(LINE, C_BLUE))
        print("  " + _step(1, 4, "登录"))
        print(clr(LINE, C_BLUE))
        print("  认证方式：" + clr(APP_SCHOOL + " 统一身份认证", C_CYAN, BOLD))
        print("  " + _hint("本工具仅适配南邮 SSO，无需选择学校；其它学校的 CAS 认证方式未知，不保证可用。"))
        print("  " + _hint("账号就是你的学号；密码输入时显示为 * 号，全角字符会自动转成半角。"))
        while not user:
            user = input("  " + clr("账号/学号", C_GREEN, BOLD) + "：").strip()
            if not user:
                print("  " + clr("! 账号不能为空，请重新输入", C_YELLOW))
        while not password:
            password = _ask_password()
            if not password:
                print("  " + clr("! 密码不能为空，请重新输入", C_YELLOW))
    return user, password


def ensure_login(args):
    """完成登录并返回 token。失败会记录错误；交互环境下可重试，返回 None 表示放弃。"""
    if args.token:
        write_log("使用已有 token（跳过 SSO 登录）")
        print("  " + clr("✓ [登录]", C_GREEN, BOLD) + " 已提供 token，跳过账号登录")
        return args.token.strip()
    while True:
        try:
            user, password = collect_login(args)
        except Exception as e:
            record_error("收集登录信息", e)
            return None
        print("  " + clr("正在登录 …", C_BLUE) + clr("（%s @ %s）" % (user, APP_SCHOOL), C_GRAY))
        write_log("开始 SSO 登录 user=%s school=%s" % (user, DEFAULT_SCHOOL))
        try:
            token = sso_login(user, password)
            write_log("SSO 登录成功（已获取 ai-poly）")
            print("  " + clr("✓ [登录成功]", C_GREEN, BOLD) + " 已通过南邮统一身份认证")
            return token
        except Exception as e:
            record_error("SSO 登录", e)
            print("  " + _hint("请确认账号密码是否正确；若密码结尾有标点，注意区分中英文标点。"))
            if not sys.stdin.isatty():
                return None
            if not _pause("\n  按回车重新输入账号密码重试，输入 q 放弃 > "):
                return None
            args.user = None
            args.password = None


def main():
    _harden_console_encoding()
    ap = argparse.ArgumentParser(description="Polymas 智能体课程全自动看课（纯 HTTP）")
    ap.add_argument("--list", action="store_true", help="登录并列出课程")
    ap.add_argument("--course", help="要看的课：序号 / courseId / 名称片段")
    ap.add_argument("--all", action="store_true", help="看账号下所有课程")
    ap.add_argument("--select", action="store_true",
                    help="交互式选择课程（默认在终端里没有 --course/--all 时自动进入）")
    ap.add_argument("--term", help="指定学期 term（默认用课程当前学期）")
    ap.add_argument("--force", action="store_true", help="忽略已完成，全部重报")
    ap.add_argument("--dry-run", action="store_true", help="只查看，不上报")
    ap.add_argument("--chunk", type=int, default=CHUNK_SEC,
                    help="上报分片步长（秒），默认 %d；0 表示不分片" % CHUNK_SEC)
    ap.add_argument("--threads", type=int, default=THREADS_DEFAULT,
                    help="并发线程数：每个视频一个线程，默认 %d，最大 %d（超出按 %d 处理）"
                         % (THREADS_DEFAULT, THREADS_MAX, THREADS_MAX))
    ap.add_argument("--realtime", action="store_true",
                    help="按真实时间间隔发送请求：等到该片真的\"看完\"才上报，"
                         "整批耗时≈视频总时长（单线程时按顺序真实播放，多线程时多视频同时真实播放）")
    ap.add_argument("--user", default=os.environ.get("ZHS_USER"), help="账号/学号（不填则启动时询问）")
    ap.add_argument("--pass", dest="password", default=os.environ.get("ZHS_PASS"),
                    help="密码（不填则启动时询问）")
    ap.add_argument("--token", default=os.environ.get("AIPOLY_TOKEN"),
                    help="已有 ai-poly 时直接使用，跳过 SSO 登录")
    ap.add_argument("--no-color", action="store_true",
                    help="纯文本输出（不加颜色，适合日志重定向/旧终端）")
    args = ap.parse_args()

    init_colors(force_off=args.no_color)
    init_logging()

    print()
    print(_box([
        clr(APP_NAME, BOLD, C_CYAN) + "  " + clr(APP_VERSION, C_GRAY),
        clr("纯 HTTP 运行 · 无需浏览器 · 新手友好", C_WHITE),
        "",
        clr("作者：", C_GRAY) + clr(APP_AUTHOR, C_GREEN, BOLD),
        clr("仓库：", C_GRAY) + clr(APP_REPO, C_BLUE),
        clr("协议：", C_GRAY) + clr(APP_LICENSE, C_YELLOW) + clr(" · 仅供学习交流", C_GRAY),
        clr("适用：", C_GRAY) + clr("南京邮电大学", C_MAGENTA, BOLD)
        + clr("（其它学校 CAS 未验证）", C_GRAY),
        clr("声明：", C_GRAY) + clr("严禁代刷收费 / 倒卖二进制！", C_RED, BOLD),
    ]))
    print()
    print("  " + clr("三步上手", BOLD, C_MAGENTA))
    print("   " + clr("1.", C_MAGENTA, BOLD) + " 按提示输入账号（学号）和密码，密码显示为 " + clr("*", C_YELLOW))
    print("   " + clr("2.", C_MAGENTA, BOLD) + " 在课程列表里输入序号选择要看的课（可多选，如 " + clr("1,3", C_CYAN) + "）")
    print("   " + clr("3.", C_MAGENTA, BOLD) + " 程序自动把视频标记为已看完，随时输入 " + clr("q", C_CYAN) + " 退出")
    print("  " + clr("可选：", C_GRAY) + "课程列表界面按 " + clr("r", C_CYAN, BOLD)
          + " 可在" + clr("压缩发送", C_YELLOW) + " / " + clr("真实时间间隔", C_GREEN)
          + " 之间切换上报节奏")
    print("  " + _hint("本程序不会保存你的账号密码，也不会联网上传任何个人信息。"))

    # 免责声明确认（按下任意键表示同意，不同意则退出）
    if not confirm_disclaimer():
        error_summary()
        sys.exit(1)
    if sys.stdout.isatty():
        print("  " + clr("2 秒后进入程序 …", C_GRAY))
        time.sleep(2)
    clear_screen()          # 首页 → 登录界面

    print()
    print("  " + clr("日志文件：%s" % LOG_PATH, C_GRAY))
    print(clr("─" * 58, C_GRAY))

    # 1) 登录
    token = ensure_login(args)
    if not token:
        error_summary()
        print("日志文件：%s" % LOG_PATH)
        _pause("\n按回车退出 ...")
        sys.exit(1)
    clear_screen()          # 登录界面 → 选课界面

    poly = Polymas(token)
    try:
        me = poly.me()
        print("\n  " + clr("✓ [身份确认]", C_GREEN, BOLD) + " %s"
              % clr(me.get("realName"), BOLD, C_WHITE)
              + clr("（账号 %s）" % me.get("userCode"), C_GRAY))
        write_log("身份校验成功 user=%s schoolNid=%s"
                  % (me.get("userCode"), me.get("schoolNid")))
    except Exception as e:
        record_error("校验身份", e)
        error_summary()
        print("日志文件：%s" % LOG_PATH)
        _pause("\n按回车退出 ...")
        sys.exit(1)

    # 一次性模式（--list / --course / --all）跑完就结束；否则交互循环，看完不退出
    one_shot = bool(args.list or args.course or args.all)
    # 上报设置：初值来自命令行，选课界面里可输入 r / safe 切换（同一个字典就地生效）
    opts = {"realtime": bool(args.realtime),
            "threads": max(1, min(THREADS_MAX, int(args.threads or THREADS_DEFAULT)))}

    # 2) 主循环
    while True:
        # 拉课程
        print("\n  " + _step(2, 4, "获取课程列表"))
        try:
            courses = poly.courses()
            write_log("拉到 %d 门课程" % len(courses))
        except Exception as e:
            record_error("获取课程列表", e)
            print("  " + _hint("通常是网络波动，按回车可以重试。"))
            if not _pause("  按回车重试获取课程，输入 q 退出 > "):
                break
            continue

        if args.list:
            print_courses(courses)
            break

        # 选课
        targets = []
        try:
            if args.all:
                targets = courses
                print_courses(courses)
            elif args.course:
                print_courses(courses)
                targets = [pick_course(courses, args.course)]
            elif args.select or sys.stdin.isatty():
                targets = choose_courses(courses, opts)
            else:
                print_courses(courses)
                record_error("选择课程", RuntimeError(
                    "非交互环境：请用 --course 指定课程，或 --all 全部，或 --list 查看"))
        except Exception as e:
            record_error("选择课程", e)
            print("  " + _hint("请检查输入的序号是否在列表范围内。"))

        if not targets:
            if one_shot:
                break
            if not _pause("  按回车返回课程列表，输入 q 退出 > "):
                break
            continue

        # 看课
        clear_screen()      # 选课界面 → 看课界面
        print("\n  " + _step(3, 4, "开始看课：共 %d 门课程" % len(targets)))
        print("  " + clr("上报节奏：", C_GRAY)
              + (clr("真实时间间隔", C_GREEN, BOLD) if opts["realtime"]
                 else clr("压缩发送", C_YELLOW, BOLD))
              + clr("    并发线程：%d" % opts["threads"], C_GRAY)
              + clr("    （可在选课界面输入 r / safe 切换节奏）", C_GRAY))
        t0 = time.time()
        cv = cd = 0
        for c in targets:
            try:
                st = brush_course(poly, c, term_arg=args.term,
                                  force=args.force, dry_run=args.dry_run,
                                  chunk=args.chunk, threads=opts["threads"],
                                  realtime=opts["realtime"])
                cv += st["total"]
                cd += st["done"]
            except Exception as e:
                record_error("看课 %s" % c.get("courseName"), e)

        print("\n" + clr("═" * 58, C_GREEN))
        print("  " + clr("本轮小结", BOLD, C_GREEN) + "  课程 %s 门　视频 %s　用时 %s　错误 %s"
              % (clr(len(targets), C_CYAN, BOLD),
                 clr("%d/%d 已完成" % (cd, cv), C_GREEN, BOLD),
                 clr("%.1fs" % (time.time() - t0), C_GRAY),
                 clr("%d 个" % len(ERRORS), C_RED if ERRORS else C_GREEN)))
        print(clr("═" * 58, C_GREEN))
        write_log("本轮完成：课程 %d，视频 %d/%d，累计错误 %d"
                  % (len(targets), cd, cv, len(ERRORS)))

        # 一次性模式结束；交互模式回到选课（看完不退出）
        if one_shot:
            break
        if not _pause("\n  按回车继续选择课程，输入 q 退出 > "):
            break
        clear_screen()      # 看课界面 → 选课界面（回到课程列表）

    # 3) 收尾：错误汇总 + 保持窗口不自动关闭
    error_summary()
    print("日志文件：%s" % LOG_PATH)
    _pause("\n按回车退出 ...")
    sys.exit(1 if ERRORS else 0)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n已取消。")
        sys.exit(130)
    except Exception as e:
        record_error("主流程", e)
        error_summary()
        print("日志文件：%s" % LOG_PATH)
        _pause("\n按回车退出 ...")
        sys.exit(1)
