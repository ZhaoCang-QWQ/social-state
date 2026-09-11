"""social_state：麦麦的关系状态表 + 感知器 + 拟人表达/生活日程（拟人化路线图 · 阶段1+2+3a）

给每个联系人记一本账：
    好感度 affinity (-100~100)  ← 感知器 LLM 语境化打分（±10 钳制）+ 手动命令
    今日心情 mood  (-50~50)    ← 同上（±25 钳制），隔天自动衰减回 0
    被冷落指数 ignore (0~100)  ← 对方不回应时缓慢累积，互动/隔天缓解
    待续线头 thread_items      ← 带到期时间的钩子列表（"周末约了漫展"）；30 天封顶，过期/兑现/聊死自动清
    互动时间戳                  ← 对方最后发言 / 麦麦最后回复 / 累计条数
    关系边 relation_edge       ← 群冲突抽取写入（"C 骂了 A"→ 敌对边），站队用

感知器（阶段2）：
    私聊：距上次评估 ≥ min_interval 秒且攒到新消息 → 一次 LLM 调用产出
          {好感±, 心情±, 线头新增(≤30天), 线头清除, 原因}，写入本表
    群聊：group_interval 秒一次 → 识别辱骂/攻击 → 写敌对关系边 + 落账（v0.4.3：
          注入人物关系背景防朋友玩梗误判 + 置信度闸门 + 站队惩罚随受害者好感缩放，陌生人打架不动账）
    打分语境化：prompt 必须带当前好感/冷落 + 最近对话——同一句话在不同关系温度下分数相反

生活日程（阶段3a）：
    每天第一条消息触发懒生成当日日程（LLM 按人设排 4-6 个时段），存 daily_schedule 表；
    回复前注入"现在这个点你大概在做 XX"；深夜自动进入"被窝"状态；/今天 命令查看全天。

两个读出口：
    1. maisaka.replyer.before_request（BLOCKING）：回复前注入关系温度 + 临期线头 + 表达约束 + 今日日程
    2. 未来主动中枢（阶段4）：冲动评分公式直接读本表

数据落盘：data/plugins/social_state/social_state.sqlite3（懒衰减/懒清理/懒生成：无后台任务）

命令：
    /关系            私聊=查自己；群里=最近互动 top5
    /关系 <QQ|昵称>   查指定的人
    /今天            查看麦麦今天的日程
    /ss_set <QQ> <affinity|mood|ignore|thread> <值>   仅操作员（operator）
    /关系帮助

设计文档：工作区《麦麦关系状态表-设计v0.1.md》（v0.2 + 阶段2 补充设计）；路线图阶段3 自研集成
"""
from __future__ import annotations

import asyncio
import hashlib
import json
import os
import random
import sqlite3
import threading
import time
from collections import OrderedDict
from datetime import datetime
from typing import Any, Dict, List, Optional, Tuple

from maibot_sdk import Command, Field, HookHandler, MaiBotPlugin, PluginConfigBase
from maibot_sdk.types import HookMode

# ── 数值边界（设计文档 v0.2 钳制） ─────────────────────────────────────────────

AFFINITY_MIN, AFFINITY_MAX = -100.0, 100.0
MOOD_MIN, MOOD_MAX = -50.0, 50.0
IGNORE_MIN, IGNORE_MAX = 0.0, 100.0

SUPPORTED_CONFIG_VERSION = "0.3.0"

# 感知器钳制（设计文档 v0.2：单次变化上限，防 LLM 打分飘）
MAX_AFFINITY_DELTA = 10.0
MAX_MOOD_DELTA = 25.0
# 线头有效期：软钩子默认天数 / 硬上限（超 30 天的"期货"感知器根本不记）
THREAD_DEFAULT_DAYS = 10
THREAD_MAX_DAYS = 30
# 消息 buffer 容量
PRIVATE_BUF_SIZE = 10
GROUP_BUF_SIZE = 20
GROUP_AT_BUF_SIZE = 40       # 群回味评估：每个群保留的最近发言上下文条数
GROUP_AUTO_BATCH_MSGS = 20   # 全群攒够这么多条消息才值得回味一次（一次 LLM 评所有人，省 token）
AT_EVAL_DELAY_MIN = 180      # 回味延迟下限（秒）：聊完过几分钟才定性，不秒结账
AT_EVAL_DELAY_MAX = 360      # 回味延迟上限（秒）：随机化，避免机械规律
GROUP_AT_BUF_KEEP = 35       # buffer 快满（40 条）时不再顺延回味，防止老消息被挤出评估窗口
AT_EVAL_FORCE_AFTER = 600    # 回味窗口最长挂起时长（秒）：超过后下一条消息/维护循环立即强制评估
LLM_CALL_TIMEOUT = 60        # LLM 调用硬熔断（秒）：宿主超时不生效时由外层强制掐断，防协程永久挂起

# session → person 缓存容量（超限淘汰最旧；防长期运行内存增长）
MAX_PRIVATE_SESSIONS = 1024
MAX_GROUP_SESSIONS = 256
MAX_GROUP_MEMBERS = 50
# 懒衰减一次最多补算的跨天数（防止系统时间被改动后出现夸张数值）
MAX_DECAY_DAYS = 7


def clamp(v: float, lo: float, hi: float) -> float:
    try:
        v = float(v)
    except Exception:
        return lo
    return max(lo, min(hi, v))


def get_person_id(platform: str, user_id: str) -> str:
    """与主程序 src/person_info/person_info.py::get_person_id 完全一致。

    platform 形如 "webchat-abc" 时取 "-" 后半段；最终 id = md5(f"{platform}_{user_id}")。
    对齐主程序意味着：本表能直接和 A_Memorix 的人物画像共用同一个 person_id。
    """
    platform = str(platform or "qq").strip() or "qq"
    user_id = str(user_id or "").strip()
    if "-" in platform:
        platform = platform.split("-")[1]
    key = f"{platform}_{user_id}"
    return hashlib.md5(key.encode("utf-8")).hexdigest()


def fmt_duration(seconds: float) -> str:
    """把秒数变成"3 分钟前"这类人话。"""
    try:
        s = max(0, int(seconds))
    except Exception:
        return "未知"
    if s < 60:
        return "刚刚"
    if s < 3600:
        return f"{s // 60} 分钟前"
    if s < 86400:
        return f"{s // 3600} 小时前"
    if s < 86400 * 30:
        return f"{s // 86400} 天前"
    return f"{s // (86400 * 30)} 个月前"


def affinity_label(v: float) -> str:
    """好感度分档文案（注入给 LLM 看的，也给人看）。"""
    if v >= 60:
        return "挚友，非常在乎"
    if v >= 30:
        return "好友，明显偏爱"
    if v >= 10:
        return "好感不错的朋友"
    if v >= 0:
        return "普通朋友"
    if v > -10:
        return "有点看不顺眼，态度偏冷"
    if v > -30:
        return "疏远，不太想理"
    if v > -60:
        return "不喜欢，很冷淡"
    return "非常讨厌，不想接触"


# ── 配置模型（WebUI 配置页据此渲染表单） ──────────────────────────────────────


class PluginSectionConfig(PluginConfigBase):
    """插件开关。"""

    __ui_label__ = "插件"
    __ui_icon__ = "package"
    __ui_order__ = 0

    enabled: bool = Field(default=True, description="是否启用插件（总开关）", json_schema_extra={"label": "插件总开关"})
    config_version: str = Field(default=SUPPORTED_CONFIG_VERSION, description="配置版本（勿改）", json_schema_extra={"hidden": True, "disabled": True})


class InjectionSectionConfig(PluginConfigBase):
    """Prompt 注入。"""

    __ui_label__ = "Prompt 注入"
    __ui_icon__ = "message-square"
    __ui_order__ = 1

    inject_private: bool = Field(default=True, description="私聊回复前，把对方的关系温度注入提示词", json_schema_extra={"label": "私聊注入"})
    inject_group: bool = Field(default=True, description="群聊回复前，把最近互动群友的关系温度注入提示词", json_schema_extra={"label": "群聊注入"})
    group_max_persons: int = Field(default=3, description="群聊注入最多列出的最近互动人数（1-5）", json_schema_extra={"label": "群聊注入人数上限", "min": 1, "max": 5})
    inject_log: bool = Field(default=False, description="每次注入时写一行日志（排查用，平时关）", json_schema_extra={"label": "注入日志"})


class BehaviorSectionConfig(PluginConfigBase):
    """统计与衰减。"""

    __ui_label__ = "统计与衰减"
    __ui_icon__ = "activity"
    __ui_order__ = 2

    track_group: bool = Field(default=True, description="是否统计群聊互动（关闭后只记私聊）", json_schema_extra={"label": "统计群聊互动"})
    mood_daily_relief: float = Field(default=1.0, description="每天心情偏移的衰减比例，0~1；1=隔天全部归零", json_schema_extra={"label": "心情隔天衰减比例", "min": 0.0, "max": 1.0, "step": 0.1})
    ignore_daily_relief: float = Field(default=10.0, description="每天被冷落指数缓解的点数，0~100", json_schema_extra={"label": "冷落指数每天缓解", "min": 0.0, "max": 100.0, "step": 1.0})
    max_events: int = Field(default=5000, description="事件流水最多保留条数（超出自动清理旧记录）", json_schema_extra={"label": "事件流水上限"})
    bot_ids: List[str] = Field(default_factory=list, description="⚠️ 填麦麦机器人自己的 QQ 号，不是你自己的！填错会把那个人发的消息全部忽略。插件会自动识别麦麦账号，此处通常留空", json_schema_extra={"label": "麦麦账号 ID（通常留空，勿填自己）"})


class PerceiverSectionConfig(PluginConfigBase):
    """感知器（阶段2：LLM 自动打分 + 线头挖掘 + 群冲突）。"""

    __ui_label__ = "感知器"
    __ui_icon__ = "brain"
    __ui_order__ = 3

    enabled: bool = Field(default=True, description="开启后由 LLM 自动评估每轮互动，自动写入好感/心情/线头（消耗少量 token）", json_schema_extra={"label": "感知器总开关"})
    model_task: str = Field(default="utils", description="LLM 任务名（model_config.toml 的 model_task_config 键），utils=轻量任务", json_schema_extra={"label": "LLM 任务名"})
    min_interval: int = Field(default=90, description="私聊评估最小间隔（秒）：攒够时间的新消息一起评，省 token", json_schema_extra={"label": "私聊评估间隔（秒）", "min": 30, "max": 1800})
    group_conflict: bool = Field(default=True, description="群聊冲突抽取：识别辱骂/攻击并记关系边（站队数据）", json_schema_extra={"label": "群冲突抽取"})
    group_interval: int = Field(default=300, description="群聊冲突评估最小间隔（秒）", json_schema_extra={"label": "群评估间隔（秒）", "min": 60, "max": 3600})
    group_auto_score: bool = Field(default=True, description="群聊自动回味评估：无需 @，全群攒够一批消息后一次 LLM 更新所有人的印象，成本可控", json_schema_extra={"label": "群聊自动评估"})
    group_auto_batch: int = Field(default=20, description="全群攒够多少条消息触发一次回味评估", json_schema_extra={"label": "群回味触发条数", "min": 5, "max": 100})
    group_auto_interval: int = Field(default=3600, description="同一人两次被回味的最小间隔（秒），防止话痨被频繁刷分", json_schema_extra={"label": "群回味间隔（秒）", "min": 300, "max": 21600})
    temperature: float = Field(default=0.3, description="打分模型温度（低=稳定）", json_schema_extra={"label": "温度", "min": 0.0, "max": 1.0, "step": 0.1})


class DailyLifeSectionConfig(PluginConfigBase):
    """生活日程（阶段3a：麦麦每天有自己的日子要过）。"""

    __ui_label__ = "生活日程"
    __ui_icon__ = "calendar"
    __ui_order__ = 4

    enabled: bool = Field(default=True, description="每天自动生成麦麦的日程，回复时注入\"你现在大概在做 XX\"，问\"在干嘛\"能答出正在干嘛", json_schema_extra={"label": "生活日程开关"})
    model_task: str = Field(default="utils", description="生成日程用的 LLM 任务名", json_schema_extra={"label": "LLM 任务名"})
    persona: str = Field(default="", description="麦麦的人设简介（身份/年龄/喜好，如：大学生，喜欢游戏和动漫，有点毒舌）。日程会严格按这个人设生成，建议填写", json_schema_extra={"label": "人设简介（强烈建议填写）"})
    wake_hour: int = Field(default=8, description="麦麦几点起床（起床前被叫=睡眼惺忪）", json_schema_extra={"label": "起床时间（点）", "min": 5, "max": 12})
    sleep_hour: int = Field(default=23, description="麦麦几点睡觉（之后被叫=在被窝里迷迷糊糊）", json_schema_extra={"label": "睡觉时间（点）", "min": 21, "max": 28})
    expression_style: bool = Field(default=True, description="表达约束：口语化短句、不写小说体、不知道的事不编造", json_schema_extra={"label": "表达约束注入"})


class ProactiveSectionConfig(PluginConfigBase):
    """主动冲动中枢（阶段4.1：让麦麦自己想找人说话，planner 终审）。"""

    __ui_label__ = "主动中枢"
    __ui_icon__ = "zap"
    __ui_order__ = 5

    enabled: bool = Field(default=False, description="开启后麦麦会基于临期线头/久未联系自主决定主动找人（planner 仍会终审，可能憋回去）。默认关，确认效果后再开", json_schema_extra={"label": "主动中枢开关"})
    model_task: str = Field(default="utils", description="（预留）冲动检查用的 LLM 任务名", json_schema_extra={"label": "LLM 任务名"})
    check_interval_min: int = Field(default=15, description="冲动检查间隔（分钟）", json_schema_extra={"label": "检查间隔（分钟）", "min": 5, "max": 120})
    min_affinity: int = Field(default=20, description="好感门槛：低于此值绝不主动（负分/陌生人一律不找）", json_schema_extra={"label": "主动好感门槛", "min": -100, "max": 100})
    daily_min: int = Field(default=2, description="每天主动次数下限（实际值在上下限间每日随机，模拟真人波动）", json_schema_extra={"label": "每日主动下限", "min": 1, "max": 10})
    daily_max: int = Field(default=3, description="每天主动次数上限（与下限组成区间，每天随机取值）", json_schema_extra={"label": "每日主动上限", "min": 1, "max": 10})
    cooldown_hours: int = Field(default=4, description="同一人两次主动之间的最小间隔（小时）", json_schema_extra={"label": "同一人冷却（小时）", "min": 1, "max": 48})
    max_ignore: int = Field(default=40, description="被冷落指数超过此值就绝不主动（被冷落会收敛）", json_schema_extra={"label": "冷落上限", "min": 0, "max": 100})


class SocialStateRootConfig(PluginConfigBase):
    """插件根配置。"""

    plugin: PluginSectionConfig = Field(default_factory=PluginSectionConfig, json_schema_extra={"label": "插件"})
    injection: InjectionSectionConfig = Field(default_factory=InjectionSectionConfig, json_schema_extra={"label": "Prompt 注入"})
    behavior: BehaviorSectionConfig = Field(default_factory=BehaviorSectionConfig, json_schema_extra={"label": "统计与衰减"})
    perceiver: PerceiverSectionConfig = Field(default_factory=PerceiverSectionConfig, json_schema_extra={"label": "感知器"})
    daily_life: DailyLifeSectionConfig = Field(default_factory=DailyLifeSectionConfig, json_schema_extra={"label": "生活日程"})
    proactive: ProactiveSectionConfig = Field(default_factory=ProactiveSectionConfig, json_schema_extra={"label": "主动中枢"})


# ── 存储层（内嵌单文件，SQLite + 懒衰减） ─────────────────────────────────────


class SocialStateStore:
    """关系状态表存储。

    表① person_state：每人一行（好感/心情/冷落/线头/互动时间）
    表② events：事件流水（审计 + 将来统计活跃度用）
    表③ relation_edge：人物关系边（站队用，阶段2 群冲突抽取写入；本阶段预留）
    """

    _SETTABLE_NUM = {"affinity": (AFFINITY_MIN, AFFINITY_MAX), "mood": (MOOD_MIN, MOOD_MAX), "ignore": (IGNORE_MIN, IGNORE_MAX)}

    def __init__(self, data_dir: str, *, mood_daily_relief: float = 1.0, ignore_daily_relief: float = 10.0):
        os.makedirs(data_dir, exist_ok=True)
        self._db_path = os.path.join(data_dir, "social_state.sqlite3")
        self._lock = threading.Lock()
        self._mood_daily_relief = clamp(mood_daily_relief, 0.0, 1.0)
        self._ignore_daily_relief = clamp(ignore_daily_relief, 0.0, 100.0)
        self._conn = sqlite3.connect(self._db_path, check_same_thread=False)
        self._conn.row_factory = sqlite3.Row
        self._create_tables()

    # ── 基础 ──

    def close(self) -> None:
        try:
            with self._lock:
                self._conn.close()
        except Exception:
            pass

    def update_params(self, *, mood_daily_relief: Optional[float] = None, ignore_daily_relief: Optional[float] = None) -> None:
        if mood_daily_relief is not None:
            self._mood_daily_relief = clamp(mood_daily_relief, 0.0, 1.0)
        if ignore_daily_relief is not None:
            self._ignore_daily_relief = clamp(ignore_daily_relief, 0.0, 100.0)

    def _create_tables(self) -> None:
        with self._lock, self._conn:
            self._conn.execute(
                """
                CREATE TABLE IF NOT EXISTS person_state (
                    person_id        TEXT PRIMARY KEY,
                    platform         TEXT NOT NULL DEFAULT '',
                    user_id          TEXT NOT NULL DEFAULT '',
                    display_name     TEXT NOT NULL DEFAULT '',
                    affinity         REAL NOT NULL DEFAULT 0,
                    mood             REAL NOT NULL DEFAULT 0,
                    ignore           REAL NOT NULL DEFAULT 0,
                    thread           TEXT NOT NULL DEFAULT '',
                    last_msg_at      REAL NOT NULL DEFAULT 0,
                    last_bot_reply_at REAL NOT NULL DEFAULT 0,
                    msg_count_total  INTEGER NOT NULL DEFAULT 0,
                    last_mood_day    TEXT NOT NULL DEFAULT '',
                    last_ignore_day  TEXT NOT NULL DEFAULT '',
                    created_at       REAL NOT NULL DEFAULT 0,
                    updated_at       REAL NOT NULL DEFAULT 0
                )
                """
            )
            self._conn.execute(
                """
                CREATE TABLE IF NOT EXISTS events (
                    id        INTEGER PRIMARY KEY AUTOINCREMENT,
                    ts        REAL NOT NULL,
                    person_id TEXT NOT NULL DEFAULT '',
                    kind      TEXT NOT NULL DEFAULT '',
                    detail    TEXT NOT NULL DEFAULT ''
                )
                """
            )
            self._conn.execute(
                """
                CREATE TABLE IF NOT EXISTS relation_edge (
                    from_person TEXT NOT NULL,
                    to_person   TEXT NOT NULL,
                    kind        TEXT NOT NULL,
                    weight      REAL NOT NULL DEFAULT 0,
                    evidence    TEXT NOT NULL DEFAULT '',
                    updated_at  REAL NOT NULL DEFAULT 0,
                    PRIMARY KEY (from_person, to_person, kind)
                )
                """
            )
            self._conn.execute(
                """
                CREATE TABLE IF NOT EXISTS thread_item (
                    id         INTEGER PRIMARY KEY AUTOINCREMENT,
                    person_id  TEXT NOT NULL,
                    content    TEXT NOT NULL,
                    hardness   TEXT NOT NULL DEFAULT 'normal',
                    created_at REAL NOT NULL,
                    due_at     REAL NOT NULL
                )
                """
            )
            self._conn.execute(
                """
                CREATE TABLE IF NOT EXISTS daily_schedule (
                    date    TEXT NOT NULL,
                    period  TEXT NOT NULL,
                    content TEXT NOT NULL,
                    PRIMARY KEY (date, period)
                )
                """
            )
            # v0.4.1：person→session 映射持久化（重启后主动中枢立即可用，无需等新消息重建）
            try:
                self._conn.execute("ALTER TABLE person_state ADD COLUMN session_id TEXT NOT NULL DEFAULT ''")
            except Exception:
                pass  # 列已存在
            self._conn.execute("CREATE INDEX IF NOT EXISTS idx_thread_person ON thread_item(person_id, due_at)")
            self._conn.execute("CREATE INDEX IF NOT EXISTS idx_events_person ON events(person_id, ts)")
            self._conn.execute("CREATE INDEX IF NOT EXISTS idx_events_ts ON events(ts)")

    # ── 懒衰减（调用方必须已持有 self._lock） ──

    @staticmethod
    def _days_between(day_a: str, day_b: str) -> int:
        try:
            a = datetime.strptime(day_a, "%Y-%m-%d").date()
            b = datetime.strptime(day_b, "%Y-%m-%d").date()
            return (b - a).days
        except Exception:
            return 0

    def _decay_row_locked(self, row: Dict[str, Any]) -> None:
        """读到谁才结算谁：心情隔天衰减回 0，冷落指数隔天线性缓解。

        好处：没有后台任务；麦麦几天不联系某人，下次读这行时按跨天数一次性补算。
        """
        now = time.time()
        today = time.strftime("%Y-%m-%d", time.localtime(now))
        changed = False

        mood_day = str(row.get("last_mood_day") or "")
        if mood_day != today:
            days = self._days_between(mood_day, today) if mood_day else 1
            days = max(1, min(days, MAX_DECAY_DAYS))
            mood = float(row.get("mood") or 0.0)
            if abs(mood) >= 0.5:
                factor = (1.0 - self._mood_daily_relief) ** days
                row["mood"] = clamp(mood * factor, MOOD_MIN, MOOD_MAX)
            row["last_mood_day"] = today
            changed = True

        ignore_day = str(row.get("last_ignore_day") or "")
        if ignore_day != today:
            days = self._days_between(ignore_day, today) if ignore_day else 1
            days = max(1, min(days, MAX_DECAY_DAYS))
            ign = float(row.get("ignore") or 0.0)
            if ign >= 0.5:
                row["ignore"] = clamp(ign - self._ignore_daily_relief * days, IGNORE_MIN, IGNORE_MAX)
            row["last_ignore_day"] = today
            changed = True

        if changed:
            row["updated_at"] = now
            self._conn.execute(
                "UPDATE person_state SET mood=?, ignore=?, last_mood_day=?, last_ignore_day=?, updated_at=? WHERE person_id=?",
                (row["mood"], row["ignore"], row["last_mood_day"], row["last_ignore_day"], now, row["person_id"]),
            )

    # ── 写入 ──

    def touch_message(self, *, person_id: str, platform: str, user_id: str, display_name: str, ts: float) -> None:
        """对方发来一条消息：建行 + 刷新昵称/最后发言/累计条数。"""
        display_name = str(display_name or "").strip() or str(user_id)
        with self._lock, self._conn:
            self._conn.execute(
                "INSERT OR IGNORE INTO person_state (person_id, platform, user_id, display_name, created_at, updated_at) VALUES (?,?,?,?,?,?)",
                (person_id, platform, str(user_id), display_name, ts, ts),
            )
            self._conn.execute(
                "UPDATE person_state SET display_name=?, last_msg_at=MAX(last_msg_at,?), msg_count_total=msg_count_total+1, updated_at=? WHERE person_id=?",
                (display_name, ts, ts, person_id),
            )

    def touch_bot_reply(self, person_id: str, ts: float) -> None:
        """麦麦给对方回了一条（私聊）。"""
        with self._lock, self._conn:
            self._conn.execute(
                "INSERT OR IGNORE INTO person_state (person_id, last_bot_reply_at, created_at, updated_at) VALUES (?,?,?,?)",
                (person_id, ts, ts, ts),
            )
            self._conn.execute(
                "UPDATE person_state SET last_bot_reply_at=MAX(last_bot_reply_at,?), updated_at=? WHERE person_id=?",
                (ts, ts, person_id),
            )

    def set_field(self, person_id: str, field: str, raw_value: str, days: Optional[float] = None) -> Tuple[bool, str]:
        """手动设置字段（/ss_set 命令）。days 仅 thread 字段使用（到期天数）。返回 (是否成功, 提示)。"""
        field = str(field or "").strip().lower()
        raw_value = str(raw_value or "").strip()
        now = time.time()
        if field in self._SETTABLE_NUM:
            lo, hi = self._SETTABLE_NUM[field]
            try:
                value = float(raw_value)
            except Exception:
                return False, f"值必须是数字（范围 {lo}~{hi}）"
            value = clamp(value, lo, hi)
            with self._lock, self._conn:
                cur = self._conn.execute("UPDATE person_state SET affinity=affinity WHERE person_id=?", (person_id,))
                if cur.rowcount == 0:
                    return False, "查无此人（先让 ta 说句话，或确认 QQ 号）"
                self._conn.execute(f"UPDATE person_state SET {field}=?, updated_at=? WHERE person_id=?", (value, now, person_id))
                row = self._conn.execute("SELECT display_name FROM person_state WHERE person_id=?", (person_id,)).fetchone()
                self._conn.execute(
                    "INSERT INTO events (ts, person_id, kind, detail) VALUES (?,?,?,?)",
                    (now, person_id, "manual_set", json.dumps({"field": field, "value": value}, ensure_ascii=False)),
                )
            name = row["display_name"] if row else person_id
            return True, f"✅ 已把 {name} 的 {field} 设为 {value:g}"
        if field == "thread":
            cleared = raw_value in ("", "无", "清除", "none", "None", "0")
            with self._lock, self._conn:
                cur = self._conn.execute("SELECT 1 FROM person_state WHERE person_id=?", (person_id,))
                if cur.fetchone() is None:
                    return False, "查无此人（先让 ta 说句话，或确认 QQ 号）"
            if cleared:
                n = self.clear_all_threads(person_id)
                self.add_event(person_id, "manual_set", json.dumps({"field": "thread", "value": ""}, ensure_ascii=False))
                return True, f"✅ 已清除线头（{n} 条）"
            eff_days = THREAD_DEFAULT_DAYS if days is None else clamp(days, 1, THREAD_MAX_DAYS)
            tid = self.add_thread(person_id, raw_value, eff_days)
            self.add_event(person_id, "manual_set", json.dumps({"field": "thread", "value": raw_value, "id": tid, "due_days": eff_days}, ensure_ascii=False))
            return True, f"✅ 线头已记录（{eff_days:g} 天内有效）：{raw_value}"
        return False, "字段只支持 affinity / mood / ignore / thread"

    # ── v0.2：thread 条目表（带到期时间） ──

    def migrate_v2(self) -> int:
        """把 v0.1 单文本 thread 字段迁移为 thread_item 条目（默认 10 天），返回迁移条数。"""
        now = time.time()
        migrated = 0
        with self._lock, self._conn:
            rows = self._conn.execute(
                "SELECT person_id, thread FROM person_state WHERE thread IS NOT NULL AND thread != ''"
            ).fetchall()
            for r in rows:
                self._conn.execute(
                    "INSERT INTO thread_item (person_id, content, hardness, created_at, due_at) VALUES (?,?,?,?,?)",
                    (r["person_id"], str(r["thread"]).strip(), "normal", now, now + THREAD_DEFAULT_DAYS * 86400),
                )
                self._conn.execute("UPDATE person_state SET thread='' WHERE person_id=?", (r["person_id"],))
                migrated += 1
        return migrated

    def add_thread(self, person_id: str, content: str, days: float = THREAD_DEFAULT_DAYS, hardness: str = "normal") -> int:
        """新增一条线头，返回条目 id。days 是"几天内适合提起"。"""
        now = time.time()
        days = clamp(days, 0.5, THREAD_MAX_DAYS)
        with self._lock, self._conn:
            cur = self._conn.execute(
                "INSERT INTO thread_item (person_id, content, hardness, created_at, due_at) VALUES (?,?,?,?,?)",
                (person_id, str(content or "").strip(), hardness, now, now + days * 86400),
            )
            return int(cur.lastrowid or 0)

    def clear_threads(self, person_id: str, ids: List[int]) -> int:
        """清除指定 id 的线头（只能清这个人的），返回清除数。"""
        if not ids:
            return 0
        clean = []
        for i in ids:
            try:
                clean.append(int(i))
            except Exception:
                continue
        if not clean:
            return 0
        ph = ",".join("?" * len(clean))
        with self._lock, self._conn:
            cur = self._conn.execute(
                f"DELETE FROM thread_item WHERE person_id=? AND id IN ({ph})",
                [person_id, *clean],
            )
            return int(cur.rowcount or 0)

    def clear_all_threads(self, person_id: str) -> int:
        with self._lock, self._conn:
            cur = self._conn.execute("DELETE FROM thread_item WHERE person_id=?", (person_id,))
            return int(cur.rowcount or 0)

    def get_active_threads(self, person_id: str) -> List[Dict[str, Any]]:
        """取未过期的线头；顺手删掉已过期的（懒清理），按临期优先（due_at 升序）。"""
        now = time.time()
        with self._lock, self._conn:
            self._conn.execute("DELETE FROM thread_item WHERE person_id=? AND due_at < ?", (person_id, now))
            cur = self._conn.execute(
                "SELECT id, content, hardness, created_at, due_at FROM thread_item WHERE person_id=? AND due_at >= ? ORDER BY due_at ASC LIMIT 10",
                (person_id, now),
            )
            return [dict(r) for r in cur.fetchall()]

    def get_edges_to(self, to_person: str) -> List[Dict[str, Any]]:
        with self._lock:
            cur = self._conn.execute("SELECT * FROM relation_edge WHERE to_person=?", (to_person,))
            return [dict(r) for r in cur.fetchall()]

    def add_event(self, person_id: str, kind: str, detail: str = "") -> None:
        with self._lock, self._conn:
            self._conn.execute(
                "INSERT INTO events (ts, person_id, kind, detail) VALUES (?,?,?,?)",
                (time.time(), person_id, kind, str(detail or "")),
            )

    def trim_events(self, max_events: int) -> None:
        max_events = max(100, int(max_events))
        with self._lock, self._conn:
            self._conn.execute(
                "DELETE FROM events WHERE id NOT IN (SELECT id FROM events ORDER BY id DESC LIMIT ?)",
                (max_events,),
            )

    # ── v0.3：当日日程 ──

    def get_schedule(self, date: str) -> List[Dict[str, str]]:
        """取某天的日程（按时段排序），无则空列表。"""
        with self._lock:
            cur = self._conn.execute(
                "SELECT period, content FROM daily_schedule WHERE date=? ORDER BY period ASC",
                (date,),
            )
            return [{"period": r["period"], "content": r["content"]} for r in cur.fetchall()]

    def get_recent_schedule_contents(self, before_date: str, days: int = 3) -> List[str]:
        """取某天之前 N 天的日程内容（防重复用），返回 ["日期 内容", ...]。"""
        out: List[str] = []
        with self._lock:
            cur = self._conn.execute(
                "SELECT date, content FROM daily_schedule WHERE date < ? ORDER BY date DESC, period ASC LIMIT ?",
                (before_date, max(1, int(days)) * 8),
            )
            for r in cur.fetchall():
                out.append(f"{r['date']} {r['content']}")
        return out

    def save_schedule(self, date: str, items: List[Dict[str, str]]) -> int:
        """覆盖写入某天的日程，返回条数。items: [{period, content}]"""
        clean = []
        for it in items or []:
            p = str((it or {}).get("period") or "").strip()
            c = str((it or {}).get("content") or "").strip()
            if p and c:
                clean.append((date, p[:32], c[:120]))
        if not clean:
            return 0
        with self._lock, self._conn:
            self._conn.execute("DELETE FROM daily_schedule WHERE date=?", (date,))
            self._conn.executemany(
                "INSERT OR REPLACE INTO daily_schedule (date, period, content) VALUES (?,?,?)",
                clean,
            )
        return len(clean)

    # ── v0.4：主动中枢辅助 ──

    def count_proactive_today(self) -> int:
        """今天已主动发起的次数（events 里 kind=proactive 的当日记录数）。"""
        day = time.strftime("%Y-%m-%d")
        day_start = time.mktime(time.strptime(day, "%Y-%m-%d"))
        with self._lock:
            cur = self._conn.execute(
                "SELECT COUNT(*) FROM events WHERE kind='proactive' AND ts >= ?",
                (day_start,),
            )
            return int(cur.fetchone()[0])

    def get_last_proactive_ts(self, person_id: str) -> float:
        """此人上次被主动找的时间（无记录返回 0）。"""
        with self._lock:
            cur = self._conn.execute(
                "SELECT MAX(ts) FROM events WHERE kind='proactive' AND person_id=?",
                (person_id,),
            )
            v = cur.fetchone()[0]
            return float(v) if v else 0.0

    def get_recent_eval_direction(self, person_id: str, n: int = 3) -> Tuple[int, int]:
        """最近 n 次 LLM 打分中正/负 delta 的条数（和解信号用）。"""
        with self._lock:
            cur = self._conn.execute(
                "SELECT detail FROM events WHERE person_id=? AND kind='llm_eval' ORDER BY id DESC LIMIT ?",
                (person_id, max(1, int(n))),
            )
            rows = cur.fetchall()
        pos = neg = 0
        for r in rows:
            try:
                d = json.loads(r["detail"])
                if float(d.get("d_aff", 0)) > 0:
                    pos += 1
                elif float(d.get("d_aff", 0)) < 0:
                    neg += 1
            except Exception:
                continue
        return pos, neg

    def set_person_session(self, person_id: str, session_id: str) -> None:
        """持久化 person→session 映射（重启后主动中枢立即可用）。"""
        with self._lock, self._conn:
            self._conn.execute(
                "UPDATE person_state SET session_id=? WHERE person_id=?",
                (session_id, person_id),
            )

    def get_all_person_sessions(self) -> Dict[str, str]:
        """读回全部持久化的 person→session 映射。"""
        with self._lock:
            cur = self._conn.execute("SELECT person_id, session_id FROM person_state WHERE session_id != ''")
            return {r["person_id"]: r["session_id"] for r in cur.fetchall()}

    def upsert_edge(self, from_person: str, to_person: str, kind: str, weight: float, evidence: str = "") -> None:
        """人物关系边（阶段2 群冲突抽取用；本阶段预留入口）。

        例：upsert_edge(麦麦视角好友A的person_id, C的person_id, "敌对", -0.8, "C在群里骂了A")
        """
        with self._lock, self._conn:
            self._conn.execute(
                """
                INSERT INTO relation_edge (from_person, to_person, kind, weight, evidence, updated_at)
                VALUES (?,?,?,?,?,?)
                ON CONFLICT(from_person, to_person, kind)
                DO UPDATE SET weight=excluded.weight, evidence=excluded.evidence, updated_at=excluded.updated_at
                """,
                (from_person, to_person, kind, clamp(weight, -1.0, 1.0), str(evidence or ""), time.time()),
            )

    def get_edges_from(self, from_person: str) -> List[Dict[str, Any]]:
        with self._lock:
            cur = self._conn.execute("SELECT * FROM relation_edge WHERE from_person=?", (from_person,))
            return [dict(r) for r in cur.fetchall()]

    def get_all_edges(self) -> List[Dict[str, Any]]:
        """全部关系边（表很小，直接全量；群冲突评估时用于注入人物关系背景）。"""
        with self._lock:
            cur = self._conn.execute("SELECT * FROM relation_edge")
            return [dict(r) for r in cur.fetchall()]

    # ── 读取 ──

    def get_person(self, person_id: str) -> Optional[Dict[str, Any]]:
        with self._lock:
            cur = self._conn.execute("SELECT * FROM person_state WHERE person_id=?", (person_id,))
            r = cur.fetchone()
            if r is None:
                return None
            row = dict(r)
            self._decay_row_locked(row)
            return row

    def get_persons(self, person_ids: List[str]) -> List[Dict[str, Any]]:
        ids = [p for p in dict.fromkeys(person_ids or []) if p]
        if not ids:
            return []
        rows: List[Dict[str, Any]] = []
        with self._lock:
            for i in range(0, len(ids), 100):
                chunk = ids[i : i + 100]
                ph = ",".join("?" * len(chunk))
                cur = self._conn.execute(f"SELECT * FROM person_state WHERE person_id IN ({ph})", chunk)
                rows.extend(dict(r) for r in cur.fetchall())
            for row in rows:
                self._decay_row_locked(row)
        return rows

    def top_persons(self, limit: int = 5) -> List[Dict[str, Any]]:
        with self._lock:
            cur = self._conn.execute(
                "SELECT * FROM person_state ORDER BY last_msg_at DESC LIMIT ?",
                (max(1, int(limit)),),
            )
            rows = [dict(r) for r in cur.fetchall()]
            for row in rows:
                self._decay_row_locked(row)
            return rows

    def apply_llm_delta(self, person_id: str, d_affinity: float, d_mood: float, reason: str) -> Optional[Tuple[float, float]]:
        """感知器打分落账：在现值上加 delta（带单次钳制），返回 (新好感, 新心情)。无此人返回 None。"""
        d_affinity = clamp(d_affinity, -MAX_AFFINITY_DELTA, MAX_AFFINITY_DELTA)
        d_mood = clamp(d_mood, -MAX_MOOD_DELTA, MAX_MOOD_DELTA)
        now = time.time()
        with self._lock, self._conn:
            cur = self._conn.execute("SELECT affinity, mood FROM person_state WHERE person_id=?", (person_id,))
            r = cur.fetchone()
            if r is None:
                return None
            old_aff = float(r["affinity"] or 0.0)
            new_aff = clamp(old_aff + d_affinity, AFFINITY_MIN, AFFINITY_MAX)
            new_mood = clamp(float(r["mood"] or 0.0) + d_mood, MOOD_MIN, MOOD_MAX)
            self._conn.execute(
                "UPDATE person_state SET affinity=?, mood=?, last_mood_day=?, updated_at=? WHERE person_id=?",
                (new_aff, new_mood, time.strftime("%Y-%m-%d", time.localtime(now)), now, person_id),
            )
            self._conn.execute(
                "INSERT INTO events (ts, person_id, kind, detail) VALUES (?,?,?,?)",
                (now, person_id, "llm_eval", json.dumps({"d_aff": d_affinity, "d_mood": d_mood, "reason": reason}, ensure_ascii=False)),
            )
        return old_aff, new_aff, new_mood

    def find_person(self, query: str) -> Optional[Dict[str, Any]]:
        """按 QQ 号 / person_id / 昵称找人（依次降级）。"""
        q = str(query or "").strip()
        if not q:
            return None
        candidates: List[Dict[str, Any]] = []
        with self._lock:
            # 1) QQ 号或 person_id 精确
            if "-" not in q and len(q) < 32:
                cur = self._conn.execute("SELECT * FROM person_state WHERE user_id=?", (q,))
                candidates.extend(dict(r) for r in cur.fetchall())
            cur = self._conn.execute("SELECT * FROM person_state WHERE person_id=?", (q,))
            candidates.extend(dict(r) for r in cur.fetchall())
            if not candidates:
                # 2) 昵称精确 → 模糊
                cur = self._conn.execute("SELECT * FROM person_state WHERE display_name=?", (q,))
                candidates.extend(dict(r) for r in cur.fetchall())
            if not candidates:
                cur = self._conn.execute("SELECT * FROM person_state WHERE display_name LIKE ? ORDER BY last_msg_at DESC LIMIT 1", (f"%{q}%",))
                candidates.extend(dict(r) for r in cur.fetchall())
        for row in candidates:
            self._decay_row_locked(row)
            return row
        return None

    def stats(self) -> Tuple[int, int]:
        with self._lock:
            n_p = self._conn.execute("SELECT COUNT(*) FROM person_state").fetchone()[0]
            n_e = self._conn.execute("SELECT COUNT(*) FROM events").fetchone()[0]
        return int(n_p), int(n_e)


# ── 感知器（阶段2） ───────────────────────────────────────────────────────────


def extract_json(text: str) -> Optional[Dict[str, Any]]:
    """从 LLM 输出中提取第一个 JSON 对象（防御式：失败返回 None，绝不抛异常）。"""
    if not text:
        return None
    start = text.find("{")
    end = text.rfind("}")
    if start < 0 or end <= start:
        return None
    try:
        data = json.loads(text[start : end + 1])
        return data if isinstance(data, dict) else None
    except Exception:
        return None


def text_from_message(message: Dict[str, Any]) -> str:
    """从序列化消息里尽量取出纯文本（优先 processed_plain_text，兜底遍历 text 组件）。"""
    txt = str(message.get("processed_plain_text") or "").strip()
    if txt:
        return txt
    raw = message.get("raw_message")
    if isinstance(raw, list):
        parts = []
        for comp in raw:
            if isinstance(comp, dict) and str(comp.get("type") or "") == "text":
                data = comp.get("data")
                if isinstance(data, dict) and data.get("text"):
                    parts.append(str(data["text"]))
        return "".join(parts).strip()
    return ""


class Perceiver:
    """感知器：私聊 LLM 语境化打分 + 线头挖掘；群聊冲突抽取。

    触发模型（省 token）：消息先进 buffer，距上次评估超过配置间隔且有新消息时，
    把攒下的消息 + 当前关系状态 + 现有钩子一起交给 LLM，一次调用产出
    {好感±, 心情±, 线头新增, 线头清除, 原因}；评估过程异步进行，绝不阻塞消息流。
    """

    def __init__(self, plugin: "SocialStatePlugin") -> None:
        self._p = plugin
        self._private_buf: "OrderedDict[str, List[Dict[str, Any]]]" = OrderedDict()
        self._group_buf: "OrderedDict[str, List[Dict[str, Any]]]" = OrderedDict()
        self._groupat_buf: "OrderedDict[str, List[Dict[str, Any]]]" = OrderedDict()  # session_id -> 最近群发言（回味用）
        self._last_eval: Dict[str, float] = {}
        self._groupat_last: Dict[str, float] = {}
        self._running: set = set()  # 正在评估的 session，防重入
        self._groupat_running: set = set()
        self._group_auto_count: Dict[str, int] = {}                   # session_id -> 距上次回味的全群消息数
        self._groupat_announced: set = set()                          # 已打印"启用"日志的 session
        self._groupat_warned: set = set()                             # 已打印"未生效"警告的 session
        self._groupat_tasks: Dict[str, "asyncio.Task"] = {}          # session_id -> 回味定时任务
        self._groupat_opened_at: Dict[str, float] = {}               # session_id -> 窗口开启时间

    # ── 配置速取 ──

    def _cfg(self) -> PerceiverSectionConfig:
        return getattr(self._p.config, "perceiver", PerceiverSectionConfig())

    def _ready(self) -> bool:
        return (
            self._p._enabled()
            and bool(getattr(self._cfg(), "enabled", True))
            and self._p._store is not None
        )

    def _buf_append(self, buf: "OrderedDict[str, List[Dict[str, Any]]]", key: str, item: Dict[str, Any], cap: int) -> None:
        lst = buf.get(key)
        if lst is None:
            buf[key] = lst = []
            while len(buf) > 128:  # 会话数上限，防内存增长
                buf.popitem(last=False)
        lst.append(item)
        while len(lst) > cap:
            lst.pop(0)
        buf.move_to_end(key)

    def _buf_take(self, buf: "OrderedDict[str, List[Dict[str, Any]]]", key: str) -> List[Dict[str, Any]]:
        items = buf.get(key) or []
        buf[key] = []
        return items

    # ── 喂食入口（由钩子调用，同步、轻量） ──

    def feed_private(self, session_id: str, person_id: str, name: str, text: str, ts: float) -> None:
        if not session_id or not text:
            return
        self._buf_append(self._private_buf, session_id, {"name": name, "text": text, "ts": ts}, PRIVATE_BUF_SIZE)
        interval = max(30, int(getattr(self._cfg(), "min_interval", 90) or 90))
        if ts - self._last_eval.get(session_id, 0.0) < interval:
            return
        if session_id in self._running:
            return
        self._last_eval[session_id] = ts
        self._running.add(session_id)
        asyncio.create_task(self._evaluate_private(session_id, person_id))

    def feed_bot_reply(self, session_id: str, text: str, ts: float) -> None:
        """麦麦自己的回复也进 buffer，评估时上下文更完整。"""
        if not session_id or not text:
            return
        self._buf_append(self._private_buf, session_id, {"name": "麦麦", "text": text, "ts": ts}, PRIVATE_BUF_SIZE)

    def feed_group(self, session_id: str, person_id: str, name: str, text: str, ts: float) -> None:
        if not session_id or not text:
            return
        self._buf_append(self._group_buf, session_id, {"name": name, "text": text, "ts": ts}, GROUP_BUF_SIZE)
        # 群回味：每条群消息都算"印象积累"，攒够条数自动开回味窗口（无需 @）
        self.feed_group_auto(session_id, person_id, name, text, ts)
        if not bool(getattr(self._cfg(), "group_conflict", True)):
            return
        interval = max(60, int(getattr(self._cfg(), "group_interval", 300) or 300))
        if ts - self._last_eval.get(session_id, 0.0) < interval:
            return
        if session_id in self._running:
            return
        self._last_eval[session_id] = ts
        self._running.add(session_id)
        asyncio.create_task(self._evaluate_group(session_id))

    def eval_pending_groups(self) -> None:
        """后台兜底：把攒着未评估的群 buffer 触发一轮评估。

        解决盲区：群评估平时由"下一条群消息"触发，若冲突发生后群里再无人说话，
        最后一批消息会永远滞留——维护循环每 5 分钟调一次本方法兜底。
        """
        if not self._ready():
            return
        self._rescue_overdue_impressions()
        if not bool(getattr(self._cfg(), "group_conflict", True)):
            return
        interval = max(60, int(getattr(self._cfg(), "group_interval", 300) or 300))
        now = time.time()
        for session_id in list(self._group_buf.keys()):
            buf = self._group_buf.get(session_id) or []
            if not buf:
                continue
            if now - self._last_eval.get(session_id, 0.0) < interval:
                continue
            if session_id in self._running:
                continue
            self._last_eval[session_id] = now
            self._running.add(session_id)
            asyncio.create_task(self._evaluate_group(session_id))

    def _rescue_overdue_impressions(self) -> None:
        """群回味兜底：窗口挂起超过 AT_EVAL_FORCE_AFTER+120 秒仍未评估时，由维护循环强制执行。

        即使 asyncio 定时任务因任何原因没跑（异常/丢失/事件循环问题），
        每 5 分钟的维护循环也能把超时窗口救回来——保证最坏情况 15 分钟内必出结果。
        """
        now = time.time()
        # 以"窗口开启记录"为准（比任务字典更可靠：任务丢了也能救回）
        for sid in list(self._groupat_opened_at.keys()):
            opened = self._groupat_opened_at.get(sid, 0.0)
            if not opened or now - opened <= AT_EVAL_FORCE_AFTER + 120:
                continue
            self._log("[群回味] session=%s 窗口超过 %d 秒未评估，由维护循环强制执行", sid[:8], int(now - opened))
            task = self._groupat_tasks.pop(sid, None)
            if task is not None and not task.done():
                task.cancel()
            asyncio.create_task(self._evaluate_group_at(sid))

    # ── prompt 构造（纯函数，可测试） ──

    def _build_private_prompt(self, name: str, row: Dict[str, Any], lines: List[str], threads: List[Dict[str, Any]]) -> str:
        now = time.time()
        aff = float(row.get("affinity") or 0.0)
        mood = float(row.get("mood") or 0.0)
        ign = float(row.get("ignore") or 0.0)
        if threads:
            thread_lines = "\n".join(
                f"- id={t['id']}：{t['content']}（还剩 {max(0, int((float(t['due_at']) - now) / 86400))} 天到期）"
                for t in threads
            )
        else:
            thread_lines = "无"
        scene_header = "【本轮对话】（按时间顺序，\"麦麦\"是机器人自己）\n"
        return (
            "你是聊天机器人麦麦的\"社交感知器\"，负责在幕后评估人际关系。请只输出 JSON。\n\n"
            f"【当前关系】对象：{name}｜好感 {aff:+.0f}（-100~100）｜今日心情偏移 {mood:+.0f}｜冷落指数 {ign:.0f}\n"
            + scene_header
            + "\n".join(f"- {ln}" for ln in lines)
            + "\n【现有话题钩子】\n" + thread_lines
            + "\n\n请评估三件事：\n"
            "1. 这次互动让麦麦对此人的好感变化（-10~10 的整数）与心情变化（-25~25 的整数）。\n"
            "   重要：分数由「内容 × 当前关系温度 × 氛围」共同决定，同一句话在不同关系下分数相反——"
            "例：\"我喜欢你\"在好感接近 0 时是尴尬负分，在暧昧期才是正分；被冷落后的主动示好要打折。\n"
            + "   还要观察麦麦自己在对话里的反应：如果麦麦已经不耐烦、生气、明确拒绝（例如说\"再这样就删好友\"），"
            "说明对方当前的行为模式在消耗好感——此时即使对方的话字面上是示好，也应扣分。"
            "重复刷屏、无视拒绝的纠缠、冒犯性玩笑，一律视为负面行为。\n"
            "2. 是否出现新的\"话题钩子\"：对方提到的、30 天内可以自然续上的约定/计划/未完话题"
            "（例：周末要去漫展、欠一顿火锅、马上要考试）。超过 30 天的承诺（\"以后\"\"明年\"\"一万年\"）一律不记。"
            "days = 几天内适合主动提起（1~30 的整数）。没有就输出 null。\n"
            "3. 现有钩子里哪些已经兑现、被聊到、或话题已死？给出要清除的 id 列表（没有就空数组）。\n\n"
            "只输出 JSON，格式：\n"
            '{"affinity": 0, "mood": 0, "reason": "一句话原因", '
            '"new_thread": null 或 {"content": "...", "days": 10}, "clear_thread_ids": []}'
        )

    def _build_group_prompt(self, lines: List[str], rel_lines: Optional[List[str]] = None) -> str:
        prompt = (
            "你是聊天机器人麦麦的\"群聊冲突感知器\"。以下是某 QQ 群最近的聊天记录：\n"
            + "\n".join(f"- {ln}" for ln in lines)
        )
        if rel_lines:
            prompt += (
                "\n\n【背景情报（麦麦账本里的现状，判断时必须参考）】\n"
                + "\n".join(f"- {ln}" for ln in rel_lines)
                + "\n（好感度含义：>=40 朋友｜20~39 认识｜<20 陌生人，0=从无互动。"
                "关系边是两人之间的已知关系。）"
            )
        prompt += (
            "\n\n请判断其中是否发生了明确的冲突：某人辱骂/人身攻击/严重针对另一人。"
            "日常拌嘴、玩笑互怼、正常争论都不算。\n"
            "判断规则（按顺序执行）：\n"
            "1. 先看关系：若攻击者与被攻击者关系好（互为好友边、好感度高、或聊天记录里明显是熟人玩梗），"
            "那么粗口、谐音梗、脏话式昵称大概率是玩笑——哪怕字面上很难听，也不算冲突。\n"
            "2. 再找双方反应的证据：\n"
            "   - 被攻击者的反应是关键：愤怒回击、翻脸、明确表示不悦、话题因此中断 = 真冲突；"
            "没有这类反应（继续玩笑、无所谓、甚至反过来玩梗）= 不算冲突。\n"
            "   - \"攻击者\"的后续表现同样重要：骂完自己先笑、补表情包、马上转移话题 = 玩梗；"
            "越骂越凶、翻旧账、揪着不放、拉其他人群嘲 = 真冲突。\n"
            "3. 证据不足宁可漏判：输出 conflict=null 即可，漏判没有惩罚，误判有惩罚。\n"
            "只输出 JSON，格式：\n"
            '{"conflict": null} 或 {"conflict": {"attacker": "攻击者昵称", "victim": "被攻击者昵称", "brief": "一句话概括"}, "confidence": 0.9}\n'
            "confidence 是你对\"这是真冲突而非玩梗\"的把握（0~1），低于 0.7 的判定会被系统忽略。"
            "attacker/victim 必须使用聊天记录里出现过的原昵称。"
        )
        return prompt

    # ── LLM 调用 ──

    async def _call_llm(self, prompt: str) -> str:
        cfg = self._cfg()
        try:
            # 硬熔断：外层 60 秒强制掐断。宿主侧 30s cap 超时并非每次都生效，
            # 曾出现调用永不返回、评估协程永久挂起（日志停在"到点评估"后无任何输出）。
            resp = await asyncio.wait_for(
                self._p.ctx.llm.generate(
                    prompt,
                    model=str(getattr(cfg, "model_task", "utils") or "utils"),
                    temperature=clamp(getattr(cfg, "temperature", 0.3), 0.0, 1.0),
                ),
                timeout=LLM_CALL_TIMEOUT,
            )
        except asyncio.TimeoutError:
            self._log("[感知器] LLM 调用硬熔断（%d 秒未返回），本轮跳过", LLM_CALL_TIMEOUT)
            return ""
        except Exception as exc:
            self._log("[感知器] LLM 调用异常: %s", exc)
            return ""
        if isinstance(resp, dict) and resp.get("success"):
            return str(resp.get("response") or "")
        self._log("[感知器] LLM 调用失败: %s", (resp or {}).get("error") if isinstance(resp, dict) else resp)
        return ""

    def _log(self, fmt: str, *args: Any) -> None:
        try:
            self._p.ctx.logger.info(fmt, *args)
        except Exception:
            pass

    # ── 评估任务 ──

    def _apply_eval_result(self, person_id: str, name: str, data: Dict[str, Any], log_prefix: str = "[感知器]") -> None:
        """把 LLM 评估结果落账（好感/心情/线头增清）并打日志。私聊与群@共用。"""
        store = self._p._store
        reason = str(data.get("reason") or "").strip()[:100]
        try:
            d_aff = float(data.get("affinity") or 0)
            d_mood = float(data.get("mood") or 0)
        except (TypeError, ValueError):
            d_aff = d_mood = 0.0
        result = store.apply_llm_delta(person_id, d_aff, d_mood, reason)
        if result is None:
            return
        old_aff, new_aff, _ = result
        extra = ""
        nt = data.get("new_thread")
        if isinstance(nt, dict) and str(nt.get("content") or "").strip():
            days = clamp(nt.get("days", THREAD_DEFAULT_DAYS), 1, THREAD_MAX_DAYS)
            tid = store.add_thread(person_id, str(nt["content"]).strip(), days, "auto")
            extra = f"｜新钩子#{tid}（{days:.0f}天）"
        clear_ids = data.get("clear_thread_ids")
        if isinstance(clear_ids, list) and clear_ids:
            n = store.clear_threads(person_id, clear_ids)
            if n:
                extra += f"｜清钩子×{n}"
        self._log("%s %s：好感 %.0f→%.0f（本次%+.0f）心情%+.0f%s（%s）",
                  log_prefix, name, old_aff, new_aff, d_aff, d_mood, extra, reason or "无备注")

    async def _evaluate_private(self, session_id: str, person_id: str) -> None:
        store = self._p._store
        try:
            items = self._buf_take(self._private_buf, session_id)
            row = store.get_person(person_id) if store else None
            if not items or row is None:
                return
            name = str(row.get("display_name") or "?")
            lines = [f"{it['name']}：{it['text']}" for it in items]
            threads = store.get_active_threads(person_id)
            prompt = self._build_private_prompt(name, row, lines, threads)
            raw = await self._call_llm(prompt)
            data = extract_json(raw)
            if data is None:
                self._log("[感知器] %s：输出无法解析，跳过本轮", name)
                return
            self._apply_eval_result(person_id, name, data, "[感知器]")
        except Exception as exc:
            self._log("[感知器] 私聊评估异常: %s", exc)
        finally:
            self._running.discard(session_id)

    # ── 群聊自动回味评估：不靠 @，麦麦自己默默记印象 ──
    # 拟人逻辑：真人不会每句话都打分，而是群里聊了一阵之后，过一会儿自己回味一次；
    # 一次回味用一个 LLM 调用更新所有给麦麦留下印象的人（大多数人平淡闲聊，不输出）。
    # 印象在聊完之后才定性（随机延迟 + 静默去抖），同一人两次回味之间有最小间隔控制成本。

    def feed_group_auto(self, session_id: str, person_id: str, name: str, text: str, ts: float) -> None:
        """普通群消息：进该群的回味 buffer，全群攒够一批消息就开一次回味窗口。"""
        if not self._ready() or not bool(getattr(self._cfg(), "group_auto_score", True)):
            if session_id not in self._groupat_warned:
                self._groupat_warned.add(session_id)
                self._log("[群回味] 自动评估未生效：session=%s（_ready=%s，group_auto_score=%s）——仅提示一次",
                          session_id[:8], self._ready(), getattr(self._cfg(), "group_auto_score", True))
            return
        batch = max(5, int(getattr(self._cfg(), "group_auto_batch", GROUP_AUTO_BATCH_MSGS) or GROUP_AUTO_BATCH_MSGS))
        if session_id not in self._groupat_announced:
            self._groupat_announced.add(session_id)
            self._log("[群回味] 自动评估已启用：session=%s，每攒 %d 条消息回味一次", session_id[:8], batch)
        self._buf_append(self._groupat_buf, session_id, {"name": name, "text": text, "ts": ts}, GROUP_AT_BUF_SIZE)
        if session_id in self._groupat_tasks and not self._groupat_tasks[session_id].done():
            opened = self._groupat_opened_at.get(session_id, 0.0)
            if len(self._groupat_buf.get(session_id) or []) >= GROUP_AT_BUF_KEEP or time.time() - opened >= AT_EVAL_FORCE_AFTER:
                # buffer 快满 或 窗口挂起超过 10 分钟：立即回味（触发瞬间的消息一条不丢）
                task = self._groupat_tasks.pop(session_id)
                if task is not None and not task.done():
                    task.cancel()
                asyncio.create_task(self._evaluate_group_at(session_id))
            else:
                self._refresh_at_window(session_id)  # 还在聊，晚点再定性
            return
        cnt = self._group_auto_count.get(session_id, 0) + 1
        self._group_auto_count[session_id] = cnt
        batch = max(5, int(getattr(self._cfg(), "group_auto_batch", GROUP_AUTO_BATCH_MSGS) or GROUP_AUTO_BATCH_MSGS))
        if cnt < batch:
            return
        self._group_auto_count[session_id] = 0
        self._open_at_window(session_id)

    def feed_bot_group_reply(self, session_id: str, text: str, ts: float) -> None:
        """麦麦在群里的回复：也进该群的回味 buffer（上下文更完整）。"""
        self._buf_append(self._groupat_buf, session_id, {"name": "麦麦", "text": text, "ts": ts}, GROUP_AT_BUF_SIZE)
        if session_id in self._groupat_tasks and not self._groupat_tasks[session_id].done():
            if len(self._groupat_buf.get(session_id) or []) >= GROUP_AT_BUF_KEEP:
                task = self._groupat_tasks.pop(session_id)
                if task is not None and not task.done():
                    task.cancel()
                asyncio.create_task(self._evaluate_group_at(session_id))
            else:
                self._refresh_at_window(session_id)

    def _open_at_window(self, session_id: str) -> None:
        self._groupat_opened_at[session_id] = time.time()
        self._log("[群回味] session=%s 攒满一批消息，开启回味窗口（静默 %d~%d 秒后评估）",
                  session_id[:8], AT_EVAL_DELAY_MIN, AT_EVAL_DELAY_MAX)
        self._refresh_at_window(session_id)

    def _refresh_at_window(self, session_id: str) -> None:
        """重置回味计时：群里还在聊就继续等，静默后才评估。"""
        old = self._groupat_tasks.get(session_id)
        if old is not None and not old.done():
            old.cancel()
        delay = random.uniform(AT_EVAL_DELAY_MIN, AT_EVAL_DELAY_MAX)
        n = len(self._groupat_buf.get(session_id) or [])
        if n % 5 == 0:  # 降噪：每 5 条打一次进度，不刷屏
            self._log("[群回味] session=%s 有新消息，回味顺延 %.0f 秒（buffer %d 条）", session_id[:8], delay, n)
        self._groupat_tasks[session_id] = asyncio.create_task(self._delayed_group_at_eval(session_id, delay))

    def _close_at_window(self, session_id: str) -> None:
        self._groupat_opened_at.pop(session_id, None)
        task = self._groupat_tasks.pop(session_id, None)
        if task is not None and not task.done():
            task.cancel()

    async def _delayed_group_at_eval(self, session_id: str, delay: float) -> None:
        try:
            await asyncio.sleep(delay)
            await self._evaluate_group_at(session_id)
        except asyncio.CancelledError:
            pass  # 还在聊，窗口被刷新属正常路径
        except Exception as exc:
            self._log("[感知器][群回味] 异常: %s", exc)
            self._close_at_window(session_id)

    async def _evaluate_group_at(self, session_id: str) -> None:
        store = self._p._store
        try:
            self._close_at_window(session_id)
            items = self._buf_take(self._groupat_buf, session_id)
            self._log("[群回味] session=%s 到点评估，取出 %d 条消息", session_id[:8], len(items))
            if not items or store is None:
                return
            lines = [f"{it['name']}：{it['text']}" for it in items]
            rel_lines = self._build_group_rel_context(items)
            prompt = self._build_group_batch_prompt(lines, rel_lines)
            raw = await self._call_llm(prompt)
            data = extract_json(raw)
            if data is None:
                self._log("[感知器][群回味] 输出无法解析，跳过本轮（%d 条消息）", len(items))
                return
            evals = data.get("evals")
            if not isinstance(evals, list):
                evals = []
            interval = max(300, int(getattr(self._cfg(), "group_auto_interval", 3600) or 3600))
            now = time.time()
            applied = 0
            for ev in evals:
                if not isinstance(ev, dict):
                    continue
                nm = str(ev.get("name") or "").strip()
                reason = str(ev.get("reason") or "").strip()[:100]
                try:
                    d_aff = float(ev.get("affinity") or 0)
                    d_mood = float(ev.get("mood") or 0)
                except (TypeError, ValueError):
                    continue
                if d_aff == 0 and d_mood == 0:
                    continue
                person = store.find_person(nm)
                if person is None:
                    self._log("[感知器][群回味] 印象对象匹配失败：%r（账本无此人）", nm)
                    continue
                pid = person["person_id"]
                if now - self._groupat_last.get(pid, 0.0) < interval:
                    continue  # 这个人刚被回味过，本轮跳过
                self._groupat_last[pid] = now
                result = store.apply_llm_delta(pid, d_aff, d_mood, f"群聊回味：{reason}")
                if result is None:
                    continue
                old_aff, new_aff, _ = result
                applied += 1
                self._log("[感知器][群回味] %s：好感 %.0f→%.0f（本次%+.0f）心情%+.0f（%s）",
                          person.get("display_name") or nm, old_aff, new_aff, d_aff, d_mood, reason or "无备注")
            self._log("[群回味] session=%s 回味完成：覆盖 %d 条消息，更新 %d 人", session_id[:8], len(items), applied)
        except Exception as exc:
            self._log("[感知器][群回味] 评估异常: %s", exc)

    def _build_group_batch_prompt(self, lines: List[str], rel_lines: Optional[List[str]] = None) -> str:
        prompt = (
            "你是聊天机器人麦麦的\"社交感知器\"，在幕后更新它对一群人的印象。"
            "以下是麦麦所在的某个 QQ 群最近的聊天记录：\n"
            + "\n".join(f"- {ln}" for ln in lines)
        )
        if rel_lines:
            prompt += (
                "\n\n【麦麦目前的印象（账本现状，判断时必须参考）】\n"
                + "\n".join(f"- {ln}" for ln in rel_lines)
                + "\n（好感度含义：>=40 朋友｜20~39 认识｜<20 陌生人，0=还没什么印象。"
                "同一句话在不同关系温度下印象变化相反：朋友的玩笑是情趣，陌生人的冒犯是真冒犯。）"
            )
        prompt += (
            "\n\n请回顾这段记录，判断哪些人在这段时间里给麦麦留下了值得记住的整体印象变化：\n"
            "1. 只输出\"有变化的人\"：有意思、暖心、帮了忙、陪你聊天、冒犯、刷屏、阴阳怪气……"
            "大多数人的平淡闲聊不值得更新，一律不要输出。\n"
            "   判断\"玩笑还是冒犯\"要看双方的后续反应：互怼后双方继续正常聊天 = 玩梗不计入；"
            "一方明显不悦、气氛冷场 = 真冒犯才扣分。\n"
            "2. affinity 是麦麦对此人好感的变化（-10~10 整数），mood 是麦麦心情变化（-25~25 整数），"
            "reason 用一句话说明。\n"
            "3. 名字必须使用聊天记录里出现过的原昵称。\n"
            "只输出 JSON，格式：\n"
            '{"evals": [{"name": "昵称", "affinity": 2, "mood": 1, "reason": "一句话原因"}]}\n'
            "没有值得更新的人就输出 {\"evals\": []}。"
        )
        return prompt

    def _build_group_rel_context(self, items: List[Dict[str, Any]]) -> List[str]:
        """把本批消息中出现的人物关系背景整理成给 LLM 的行为锚点行。

        只描述账本里已有记录的人（陌生人没有信息，注水反而干扰判断）。
        """
        store = self._p._store
        if store is None:
            return []
        names = list(dict.fromkeys(str(it.get("name") or "").strip() for it in items))
        names = [n for n in names if n]
        found: Dict[str, Dict[str, Any]] = {}
        for nm in names:
            p = store.find_person(nm)
            if p is not None:
                found[nm] = p
        if not found:
            return []
        rel: List[str] = []
        for nm, p in found.items():
            aff = float(p.get("affinity") or 0.0)
            tier = "朋友" if aff >= 40 else ("认识" if aff >= 20 else "陌生人")
            rel.append(f"{nm}：麦麦对其好感 {aff:.0f}（{tier}）")
        pid_to_name = {p["person_id"]: nm for nm, p in found.items()}
        for e in store.get_all_edges():
            a = pid_to_name.get(e.get("from_person"))
            b = pid_to_name.get(e.get("to_person"))
            if a and b:
                rel.append(f"{a} 与 {b} 之间存在「{e.get('kind')}」边（权重{float(e.get('weight') or 0):.1f}，已知证据：{str(e.get('evidence') or '')[:40]}）")
        return rel

    async def _evaluate_group(self, session_id: str) -> None:
        store = self._p._store
        try:
            items = self._buf_take(self._group_buf, session_id)
            if not items:
                return
            lines = [f"{it['name']}：{it['text']}" for it in items]
            # 关系背景：本批消息中出现的人的好感度 + 他们之间已有的关系边
            rel_lines = self._build_group_rel_context(items)
            self._log("[群评估] session=%s 攒了 %d 条消息，开始评估（背景 %d 条）", session_id[:8], len(items), len(rel_lines))
            raw = await self._call_llm(self._build_group_prompt(lines, rel_lines))
            data = extract_json(raw)
            conflict = data.get("conflict") if data else None
            if data is not None and conflict is None:
                self._log("[群评估] 完成：未识别冲突（%d 条消息）", len(items))
            if not isinstance(conflict, dict):
                return
            # 置信度闸门：LLM 不太确定的"冲突"直接忽略（防朋友玩梗误判）
            try:
                confidence = float(data.get("confidence", 1.0))
            except (TypeError, ValueError):
                confidence = 1.0
            if confidence < 0.7:
                self._log("[群评估] 疑似冲突但置信度低（%.2f < 0.70），忽略", confidence)
                return
            attacker_name = str(conflict.get("attacker") or "").strip()
            victim_name = str(conflict.get("victim") or "").strip()
            brief = str(conflict.get("brief") or "").strip()[:100]
            if not attacker_name or not victim_name or attacker_name == victim_name:
                self._log("[群评估] 识别到冲突但角色名不完整（attacker=%r victim=%r）", attacker_name, victim_name)
                return
            attacker = store.find_person(attacker_name)
            victim = store.find_person(victim_name)
            if attacker is None or victim is None or attacker["person_id"] == victim["person_id"]:
                self._log("[群评估] 识别到冲突但账本匹配失败：attacker=%r(%s) victim=%r(%s)",
                          attacker_name, "找到" if attacker else "未找到", victim_name, "找到" if victim else "未找到")
                return
            # 站队原则：惩罚强度随"被攻击者与麦麦的关系"缩放。
            # 陌生人之间的冲突只记关系边（图谱事实），不动麦麦对攻击者的好感——
            # 麦麦没理由替一个自己不认识的人记仇。
            v_aff = float(victim.get("affinity") or 0.0)
            if v_aff >= 20:
                edge_w = -0.8
                atk_d = -clamp(round(v_aff * 0.25), 3, 10)      # 认识 -3 起步，好友最高 -10
                atk_m = -clamp(round(v_aff * 0.4), 5, 15)       # 心情同理缩放
                vic_m = clamp(round(v_aff * 0.3), 3, 10)        # 被攻击者是熟人，才值得同情
            else:
                edge_w = -0.3
                atk_d = atk_m = vic_m = 0
            store.upsert_edge(victim["person_id"], attacker["person_id"], "敌对", edge_w, brief)
            if atk_d:
                store.apply_llm_delta(attacker["person_id"], atk_d, atk_m,
                                      f"在群里攻击了麦麦的熟人 {victim_name}（好感{v_aff:.0f}）")
            if vic_m:
                store.apply_llm_delta(victim["person_id"], 0, vic_m, f"在群里被 {attacker_name} 攻击")
            store.add_event(victim["person_id"], "group_conflict", json.dumps({"attacker": attacker_name, "brief": brief}, ensure_ascii=False))
            self._log("[感知器] 群冲突：%s → %s（%s）｜受害者好感%.0f→边权重%.1f｜攻击者%+.0f/%+.0f，已落账",
                      attacker_name, victim_name, brief, v_aff, edge_w, atk_d, atk_m)
        except Exception as exc:
            self._log("[群评估] 异常: %s", exc)
        finally:
            self._running.discard(session_id)


# ── 生活日程（阶段3a：麦麦每天有自己的日子要过） ─────────────────────────────

WEEKDAY_CN = ("周一", "周二", "周三", "周四", "周五", "周六", "周日")

# 每日随机基调池：生成日程时随机抽一条，强制每天过的不是同一种日子
DAY_TWISTS = (
    "今天突然特别有精神，做什么都效率很高",
    "今天有点丧，干什么都提不起劲",
    "今天就想彻底宅着，谁也别约我",
    "今天天气不错，有点想出门走走",
    "今天在赶一件一直拖着没做的事",
    "今天胃口特别好，满脑子都在琢磨吃什么",
    "今天有点无聊，想找点新鲜事干",
    "今天莫名烦躁，看啥都不顺眼",
    "今天被一件小事逗得很开心",
    "今天犯懒癌晚期，能躺着绝不坐着",
    "今天有心事，做事总是走神",
    "今天突然特别想吃一样东西，念念不忘",
    "今天翻到了以前的东西，有点怀旧",
    "今天手气/运气莫名的好，做什么都顺",
    "今天困得不行，满脑子都是补觉",
)


def parse_period_start_end(period: str) -> Optional[Tuple[int, int]]:
    """解析 "08:00-10:00" 为 (起始小时, 结束小时)；解析失败返回 None。"""
    try:
        parts = str(period).split("-")
        sh = int(str(parts[0]).split(":")[0])
        eh = int(str(parts[1]).split(":")[0])
        if 0 <= sh <= 24 and 0 <= eh <= 24:
            return sh, max(eh, sh + 1)
    except Exception:
        pass
    return None


class DailyLife:
    """生活日程引擎：每天懒生成一份日程，回复前注入"你现在大概在做 XX"。

    无后台任务：当天第一次需要注入时若还没有日程，异步触发 LLM 生成（当次回复先不注，
    生成完落库，之后的回复就有了）。深夜/清晨不走日程表，直接给"被窝状态"。
    """

    def __init__(self, plugin: "SocialStatePlugin") -> None:
        self._p = plugin
        self._generating: set = set()  # 正在生成的日期，防重入

    def _cfg(self) -> DailyLifeSectionConfig:
        return getattr(self._p.config, "daily_life", DailyLifeSectionConfig())

    def _ready(self) -> bool:
        return self._p._enabled() and bool(getattr(self._cfg(), "enabled", True)) and self._p._store is not None

    # ── 当前状态（纯函数为主，可测试） ──

    def night_state(self, hour: int) -> Optional[str]:
        """起床前/睡觉后的固定状态；正常日间返回 None。

        sleep_hour 支持 21~28：>24 表示凌晨才睡（28 = 凌晨 4 点）。
        """
        wake = int(clamp(getattr(self._cfg(), "wake_hour", 8), 5, 12))
        sleep = int(clamp(getattr(self._cfg(), "sleep_hour", 23), 21, 28))
        bed = sleep if sleep <= 24 else sleep - 24  # 实际躺下的钟点
        if not (bed <= hour or hour < wake):
            return None
        if hour < wake:
            return "在睡觉，睡得正沉"
        return "在被窝里刷手机，迷迷糊糊快睡着了"

    def current_activity(self, items: List[Dict[str, str]], now_hour: int) -> Optional[str]:
        """从当天日程里找当前时段的活动；间隙时段算上一个时段的延续。"""
        best: Optional[str] = None
        for it in items:
            span = parse_period_start_end(it.get("period") or "")
            if span is None:
                continue
            sh, eh = span
            if sh <= now_hour < eh:
                return str(it.get("content") or "")
            if sh <= now_hour:
                best = str(it.get("content") or "")
        return best

    def life_block(self) -> str:
        """组装【表达约束】+【你今天的生活】注入段；不启用/没数据时返回空串。"""
        cfg = self._cfg()
        parts: List[str] = []
        if bool(getattr(cfg, "expression_style", True)):
            parts.append(
                "【表达约束】像真人一样说话：口语化、短句，一次只说一两句，不写书面语和小说式描写；"
                "不确定的事不要编造，不知道就承认不知道。"
            )
        if not self._ready():
            return "\n".join(parts)
        now = time.time()
        local = time.localtime(now)
        hour = local.tm_hour
        date = time.strftime("%Y-%m-%d", local)
        store = self._p._store
        assert store is not None
        items = store.get_schedule(date)
        if not items:
            self._ensure_generate(date)
            return "\n".join(parts)
        night = self.night_state(hour)
        if night is not None:
            parts.append(f"【你今天的生活】现在这个点（{hour} 点）你{night}，回复会慢、会很困。")
            return "\n".join(parts)
        act = self.current_activity(items, hour)
        if act:
            parts.append(f"【你今天的生活】现在这个点（{hour} 点）你大概正在：{act}。被问到\"在干嘛\"就按这个自然回答。")
        return "\n".join(parts)

    def _ensure_generate(self, date: str) -> None:
        if date in self._generating:
            return
        self._generating.add(date)
        asyncio.create_task(self._generate_today(date))

    # ── 生成 ──

    def _build_generate_prompt(self, date: str, weekday: str, wake: int, sleep: int, persona: str,
                              twist: str = "", recent_lines: Optional[List[str]] = None) -> str:
        who = persona.strip()
        persona_line = (
            f"你是\"麦麦\"（{who}）。日程活动必须符合这个人设的身份、年龄和生活习惯，不要出戏。"
            if who
            else "你是\"麦麦\"，一个普通的年轻人。"
        )
        end_hour = min(sleep, 24)
        lines = [
            f"{persona_line}今天是 {date}（{weekday}）。",
        ]
        if twist:
            lines.append(f"【今日随机基调】{twist}——今天的日程可以往这个状态靠，但日常该干嘛还是干嘛，别演成偶像剧。")
        if recent_lines:
            lines.append(
                "【最近几天的生活】（供参考——真人生活本来就常常重复，连续几天差不多是正常的，不必刻意求变；"
                "只有连着好几天一模一样时，才可以偶尔加点小变化）：\n"
                + "\n".join(f"- {ln}" for ln in recent_lines)
            )
        lines.append(
            f"请给麦麦安排今天 {wake:02d}:00-{end_hour:02d}:00 的日常：4-6 个时段，每个时段一句口语化的描述"
            "（像真实年轻人的日常：吃饭、上课/上班、摸鱼、打游戏、看动漫、刷手机、午睡、点外卖、追更……"
            "可以有具体细节但别浮夸）。"
        )
        lines.append("只输出 JSON 数组：[{\"period\":\"08:00-10:00\",\"content\":\"...\"},...]")
        return "\n".join(lines)

    async def _generate_today(self, date: str) -> None:
        store = self._p._store
        try:
            cfg = self._cfg()
            local = time.localtime()
            # 周几要从 date 反推：跨午夜触发时（23:59 触发、00:00 执行）local 已是第二天
            try:
                weekday = WEEKDAY_CN[time.strptime(date, "%Y-%m-%d").tm_wday]
            except Exception:
                weekday = WEEKDAY_CN[int(local.tm_wday)]
            wake = int(clamp(getattr(cfg, "wake_hour", 8), 5, 12))
            sleep = int(clamp(getattr(cfg, "sleep_hour", 23), 21, 28))
            # 随机基调按真人节奏低频出现：约 30% 的天有特殊状态，其余就是平常的一天。
            # 真人生活 = 高频重复 + 偶尔意外，每天都来一个"今日主题"反而假。
            twist = random.choice(DAY_TWISTS) if random.random() < 0.3 else ""
            recent = store.get_recent_schedule_contents(date, 3)
            prompt = self._build_generate_prompt(
                date, weekday, wake, sleep, str(getattr(cfg, "persona", "") or ""), twist, recent
            )
            resp = await self._p.ctx.llm.generate(
                prompt,
                model=str(getattr(cfg, "model_task", "utils") or "utils"),
                temperature=0.9,
            )
            text = str(resp.get("response") or "") if isinstance(resp, dict) and resp.get("success") else ""
            start = text.find("[")
            end = text.rfind("]")
            if start < 0 or end <= start:
                self._log("[生活日程] %s 生成失败：LLM 输出无法解析", date)
                return
            try:
                raw = json.loads(text[start : end + 1])
            except Exception:
                self._log("[生活日程] %s 生成失败：JSON 解析失败", date)
                return
            items = [it for it in raw if isinstance(it, dict)] if isinstance(raw, list) else []
            n = store.save_schedule(date, items) if store else 0
            self._log("[生活日程] %s 日程已生成（%d 个时段）" if n else "[生活日程] %s 生成结果为空", date, n)
        except Exception as exc:
            self._log("[生活日程] 生成异常: %s", exc)
        finally:
            self._generating.discard(date)

    def _log(self, fmt: str, *args: Any) -> None:
        try:
            self._p.ctx.logger.info(fmt, *args)
        except Exception:
            pass


# ── 主动冲动中枢（阶段4.1） ──────────────────────────────────────────────────


class ProactiveHub:
    """主动冲动中枢：定时检查"有没有值得主动的理由"，有就把冲动递给 planner。

    设计原则（呼应总路线图）：
    - 无配额，只有保险丝：每天上限 + 同人冷却只是安全网，正常情况下由条件门槛自然限流
    - planner 终审：本类只递冲动（trigger_proactive + intent 由头），说不说由 planner 决定，
      "憋回去"是拟人的一部分
    - 被冷落会收敛：冷落指数高、好感低、深夜等条件直接跳过
    """

    def __init__(self, plugin: "SocialStatePlugin") -> None:
        self._p = plugin
        self._task: Optional[asyncio.Task] = None
        self._running = False

    def _cfg(self) -> ProactiveSectionConfig:
        return getattr(self._p.config, "proactive", ProactiveSectionConfig())

    def _ready(self) -> bool:
        return (
            self._p._enabled()
            and bool(getattr(self._cfg(), "enabled", False))
            and self._p._store is not None
        )

    # ── 生命周期 ──

    def start(self) -> None:
        if self._running or not self._ready():
            return
        self._running = True
        self._task = asyncio.create_task(self._loop())
        self.ctx_log("[主动中枢] 已启动：每 %d 分钟检查一次冲动", int(getattr(self._cfg(), "check_interval_min", 15) or 15))

    def stop(self) -> None:
        self._running = False
        if self._task is not None:
            self._task.cancel()
            self._task = None

    def ctx_log(self, fmt: str, *args: Any) -> None:
        try:
            self._p.ctx.logger.info(fmt, *args)
        except Exception:
            pass

    async def _loop(self) -> None:
        base_min = max(5, int(getattr(self._cfg(), "check_interval_min", 15) or 15))
        while self._running:
            try:
                # 检查间隔加 ±20% 抖动：固定整点检查本身就不拟人
                jittered = base_min * random.uniform(0.8, 1.2)
                await asyncio.sleep(jittered * 60)
                if not self._running or not self._ready():
                    continue
                await self.check_once()
            except asyncio.CancelledError:
                break
            except Exception as exc:
                self.ctx_log("[主动中枢] 检查异常: %s", exc)
                await asyncio.sleep(60)

    # ── 冲动检查 ──

    async def check_once(self) -> None:
        store = self._p._store
        cfg = self._cfg()
        if store is None:
            return
        # 保险丝 1：每日上限——在 [下限, 上限] 区间内每日随机取值（真人主动频率有日间波动）
        d_min = max(1, int(getattr(cfg, "daily_min", 2) or 2))
        d_max = max(d_min, int(getattr(cfg, "daily_max", 3) or 3))
        # 当日额度按日期做种子：一天之内稳定不变。
        # （否则每 15 分钟检查时重掷一次，额度形同虚设，日志也会自相矛盾）
        daily_limit = random.Random(int(time.strftime("%Y%m%d"))).randint(d_min, d_max)
        done_today = store.count_proactive_today()
        if done_today >= daily_limit:
            self.ctx_log("[主动中枢] 本轮跳过：今日主动已达上限（已发 %d 次，今日额度 %d）", done_today, daily_limit)
            return

        min_aff = int(getattr(cfg, "min_affinity", 20) or 20)
        max_ign = float(getattr(cfg, "max_ignore", 40) or 40)
        cooldown_s = max(1, int(getattr(cfg, "cooldown_hours", 4) or 4)) * 3600
        now = time.time()

        # 候选人 = 有 session 映射的私聊联系人（近期有过互动的）
        candidates: List[Tuple[str, str]] = list(self._p._person_sessions.items())
        if not candidates:
            self.ctx_log("[主动中枢] 本轮跳过：候选人为空（重启后还没有普通消息建立映射，先和麦麦聊一句）")
            return
        skipped = {"好感低": 0, "被冷落": 0, "冷却中": 0, "深夜": 0, "对话中": 0}

        # 按线头紧急度收集冲动
        best: Optional[Tuple[float, str, str, str]] = None  # (urgency, person_id, session_id, intent)
        for person_id, session_id in candidates:
            row = store.get_person(person_id)
            if row is None:
                continue
            aff = float(row.get("affinity") or 0.0)
            ign = float(row.get("ignore") or 0.0)
            # 对话中 = 对方最近 5 分钟内说过话（球在麦麦这边等对方回）。
            # 注意只看对方：麦麦自己回复/命令回复不该续命"对话中"——对方没接话时，
            # 主动再提一句恰恰是自然的（否则命令回复会让判据死循环）。
            last_msg = float(row.get("last_msg_at") or 0.0)
            if now - last_msg < 300:
                skipped["对话中"] += 1
                continue
            hour = time.localtime().tm_hour
            if aff < min_aff:
                skipped["好感低"] += 1
                continue
            if ign > max_ign:
                skipped["被冷落"] += 1
                continue
            if hour >= 23 or hour < 8:
                skipped["深夜"] += 1
                continue
            # 保险丝 2：同人冷却
            last = store.get_last_proactive_ts(person_id)
            if last and now - last < cooldown_s:
                skipped["冷却中"] += 1
                continue

            urgency = 0.0
            intent_topic = ""
            # 由头①：临期线头（最硬）
            threads = store.get_active_threads(person_id)
            urgent = [t for t in threads if (float(t["due_at"]) - now) < 72 * 3600]
            if urgent:
                t = urgent[0]
                days_left = max(0, int((float(t["due_at"]) - now) / 86400))
                urgency = 0.9 if days_left <= 1 else 0.7
                intent_topic = f"有条快过期的心事想问 ta：{t['content']}（还剩 {days_left} 天）"
            # 由头②：适度沉默后的自然问候（2~7 天没说话，且好感不错）
            last_msg = float(row.get("last_msg_at") or 0.0)
            silence_days = (now - last_msg) / 86400 if last_msg else 99
            if 2 <= silence_days <= 7 and aff >= 40 and urgency < 0.5:
                urgency = 0.5
                intent_topic = f"和 {row.get('display_name')} 已经 {int(silence_days)} 天没聊了，随口问候一下近况"
            if urgency <= 0 or not intent_topic:
                continue

            name = str(row.get("display_name") or "朋友")
            intent = (
                f"你有点想主动找 {name} 说话。由头：{intent_topic}。"
                "自然地提起，别生硬，别暴露任何计划感；如果你觉得此刻不合适，完全可以不说。"
            )
            if best is None or urgency > best[0]:
                best = (urgency, person_id, session_id, intent)

        if best is None:
            self.ctx_log("[主动中枢] 本轮无人过闸（候选 %d 人，跳过原因：%s）", len(candidates), skipped)
            return
        _, person_id, session_id, intent = best
        name = "?"
        row = store.get_person(person_id)
        if row:
            name = str(row.get("display_name") or "?")
        self.ctx_log("[主动中枢] 冲动过闸：向 %s 递出由头（当日第 %d 次）", name, store.count_proactive_today() + 1)
        store.add_event(person_id, "proactive", intent[:100])
        prev_reply_ts = float((store.get_person(person_id) or {}).get("last_bot_reply_at") or 0.0)
        try:
            await self._p.ctx.maisaka.trigger_proactive(
                stream_id=session_id,
                intent=intent,
                reason="social_state 线头/沉默冲动",
                priority="normal",
            )
        except Exception as exc:
            self.ctx_log("[主动中枢] 触发失败（不影响运行）: %s", exc)
            return
        # 落锤复查：planner 模型可能"想完不落锤"（只有思考无 tool call），
        # 90 秒后确认没回复就重递一次冲动——不绕过终审，只是再敲一次门
        asyncio.create_task(self._retry_if_silent(person_id, session_id, prev_reply_ts=prev_reply_ts, intent=intent))

    async def _retry_if_silent(self, person_id: str, session_id: str, *, prev_reply_ts: float, intent: str) -> None:
        await asyncio.sleep(90)
        store = self._p._store
        if store is None or not self._running:
            return
        row = store.get_person(person_id)
        if row is None:
            return
        cur_reply = float(row.get("last_bot_reply_at") or 0.0)
        if cur_reply > prev_reply_ts:
            self.ctx_log("[主动中枢] 复查：planner 已回复，无需重试")
            return
        self.ctx_log("[主动中枢] 复查：90 秒内未回复，重递一次冲动")
        store.add_event(person_id, "proactive", "retry")
        try:
            await self._p.ctx.maisaka.trigger_proactive(
                stream_id=session_id,
                intent=intent + "（这次请务必给出一句回复，哪怕很短）",
                reason="social_state 冲动重试",
                priority="normal",
            )
        except Exception as exc:
            self.ctx_log("[主动中枢] 重试触发失败: %s", exc)


# ── 插件主体 ──────────────────────────────────────────────────────────────────


class SocialStatePlugin(MaiBotPlugin):
    """关系状态表插件：观察消息流记帐，回复前注入关系温度。"""

    config_model = SocialStateRootConfig

    def __init__(self) -> None:
        super().__init__()
        self._store: Optional[SocialStateStore] = None
        # session_id → person_id（私聊）：回复 hook 只有 session_id，靠这里反查是谁
        self._private_sessions: "OrderedDict[str, str]" = OrderedDict()
        # session_id → [person_id...]（群聊，最近的在末尾）：群聊注入在场人员
        self._group_sessions: "OrderedDict[str, List[str]]" = OrderedDict()
        self._bot_uid: str = ""  # 从消息流 additional_config.self_id 自动学习
        self._event_counter = 0
        self._perceiver = Perceiver(self)
        self._life = DailyLife(self)
        self._hub = ProactiveHub(self)
        self._person_sessions: Dict[str, str] = {}  # person_id → 最新私聊 session（主动触发反查用）
        self._maint_task: Optional[asyncio.Task] = None  # 维护循环：群评估兜底等

    # ── 生命周期（加载器契约：三个都必须实现） ──

    async def on_load(self) -> None:
        data_dir = self._data_dir()
        behavior = getattr(self.config, "behavior", None)
        self._store = SocialStateStore(
            data_dir,
            mood_daily_relief=float(getattr(behavior, "mood_daily_relief", 1.0) or 1.0),
            ignore_daily_relief=float(getattr(behavior, "ignore_daily_relief", 10.0) or 10.0),
        )
        n_persons, n_events = self._store.stats()
        migrated = self._store.migrate_v2()
        perceiver_on = bool(getattr(getattr(self.config, "perceiver", None), "enabled", True))
        life_on = bool(getattr(getattr(self.config, "daily_life", None), "enabled", True))
        proact_on = bool(getattr(getattr(self.config, "proactive", None), "enabled", False))
        self.ctx.logger.info(
            "[关系状态表] 已加载（v0.4 感知器%s｜生活日程%s｜主动中枢%s）：数据=%s | 已记 %d 人 / %d 条事件%s",
            "开" if perceiver_on else "关",
            "开" if life_on else "关",
            "开" if proact_on else "关",
            os.path.join(data_dir, "social_state.sqlite3"),
            n_persons,
            n_events,
            f" | 迁移旧线头 {migrated} 条" if migrated else "",
        )
        if proact_on:
            # 恢复持久化的 person→session 映射：重启后主动中枢立即可用
            try:
                restored = self._store.get_all_person_sessions()
                self._person_sessions.update(restored)
                if restored:
                    self.ctx.logger.info("[关系状态表] 已恢复 %d 条联系人映射（重启不失忆）", len(restored))
            except Exception as exc:
                self.ctx.logger.warning("[关系状态表] 映射恢复失败: %s", exc)
            self._hub.start()
        # 维护循环：兜底评估滞留的群消息（与主动中枢独立，插件开着就跑）
        if self._maint_task is None or self._maint_task.done():
            self._maint_task = asyncio.create_task(self._maintenance_loop())
        if perceiver_on:
            _per = getattr(self.config, "perceiver", None)
            self.ctx.logger.info(
                "[关系状态表] 感知器：LLM 任务=%s｜私聊评估间隔 %ss｜群冲突抽取 %s｜群聊回味 %s（每 %s 条）"
                "（注意：新增 llm.generate 能力需重启麦麦生效）",
                getattr(_per, "model_task", "utils"),
                getattr(_per, "min_interval", 90),
                "开" if getattr(_per, "group_conflict", True) else "关",
                "开" if getattr(_per, "group_auto_score", True) else "关",
                getattr(_per, "group_auto_batch", GROUP_AUTO_BATCH_MSGS),
            )

    async def _maintenance_loop(self) -> None:
        """维护循环：每 5 分钟兜底处理滞留事务（群评估等），与主动中枢独立。"""
        while True:
            try:
                await asyncio.sleep(300)
                if not self._enabled():
                    continue
                per = getattr(self, "_perceiver", None)
                if per is not None and self._store is not None:
                    per.eval_pending_groups()
            except asyncio.CancelledError:
                break
            except Exception as exc:
                try:
                    self.ctx.logger.warning("[关系状态表] 维护循环异常: %s", exc)
                except Exception:
                    pass

    async def on_unload(self) -> None:
        self._hub.stop()
        if self._maint_task is not None:
            self._maint_task.cancel()
            self._maint_task = None
        if self._store is not None:
            self._store.close()
            self._store = None
        self._private_sessions.clear()
        self._group_sessions.clear()
        self._person_sessions.clear()
        self.ctx.logger.info("[关系状态表] 已卸载")

    async def on_config_update(self, scope: str, config_data: dict, version: str) -> None:
        if scope != "self":
            return
        behavior = getattr(self.config, "behavior", None)
        if self._store is not None and behavior is not None:
            self._store.update_params(
                mood_daily_relief=float(getattr(behavior, "mood_daily_relief", 1.0) or 1.0),
                ignore_daily_relief=float(getattr(behavior, "ignore_daily_relief", 10.0) or 10.0),
            )
        # 主动中枢开关同步
        if bool(getattr(getattr(self.config, "proactive", None), "enabled", False)):
            self._hub.start()
        else:
            self._hub.stop()
        self.ctx.logger.info("[关系状态表] 配置已更新（衰减参数/主动中枢实时生效）")

    def _data_dir(self) -> str:
        try:
            return str(self.ctx.paths.data_dir)
        except Exception:
            return os.path.join("data", "plugins", "social_state")

    def _enabled(self) -> bool:
        return bool(getattr(self.config.plugin, "enabled", True)) and self._store is not None

    # ── session 缓存（LRU 防内存增长） ──

    def _remember_private(self, session_id: str, person_id: str) -> None:
        if not session_id:
            return
        self._private_sessions[session_id] = person_id
        self._private_sessions.move_to_end(session_id)
        while len(self._private_sessions) > MAX_PRIVATE_SESSIONS:
            self._private_sessions.popitem(last=False)
        self._person_sessions[person_id] = session_id  # 反向映射：主动中枢按人找流
        if self._store is not None:
            try:
                self._store.set_person_session(person_id, session_id)  # 持久化：重启不再失忆
            except Exception:
                pass

    def _remember_group(self, session_id: str, person_id: str) -> None:
        if not session_id:
            return
        members = self._group_sessions.get(session_id)
        if members is None:
            members = []
            self._group_sessions[session_id] = members
            while len(self._group_sessions) > MAX_GROUP_SESSIONS:
                self._group_sessions.popitem(last=False)
        if person_id in members:
            members.remove(person_id)
        members.append(person_id)
        while len(members) > MAX_GROUP_MEMBERS:
            members.pop(0)

    # ── 钩子1：收到消息（旁路记帐） ──

    @HookHandler("chat.receive.after_process", mode=HookMode.OBSERVE)
    async def on_receive(self, message: Optional[Dict[str, Any]] = None, **kwargs: Any):
        try:
            if not self._enabled() or not isinstance(message, dict):
                return
            if message.get("is_notify") or message.get("is_command"):
                return  # 戳一戳/撤回等通知、命令消息不记帐
            info = message.get("message_info") or {}
            user_info = info.get("user_info") or {}
            user_id = str(user_info.get("user_id") or "").strip()
            if not user_id:
                return
            # 官方陷阱清单 §13-11：NapCat 每条消息 additional_config 都带 self_id（麦麦自己的账号），
            # 自动学习并排除，避免把麦麦自己的消息记到别人账上；bot_ids 配置作为兜底。
            add_cfg = info.get("additional_config") or {}
            self_id = ""
            if isinstance(add_cfg, dict):
                self_id = str(add_cfg.get("self_id") or "").strip()
            if self_id and not self._bot_uid:
                self._bot_uid = self_id
                self.ctx.logger.info("[关系状态表] 已识别麦麦账号 self_id=%s（此后自动排除）", self_id)
            if (self_id and user_id == self_id) or (self._bot_uid and user_id == self._bot_uid):
                return
            bot_ids = set(getattr(self.config.behavior, "bot_ids", []) or [])
            if user_id in bot_ids:
                return

            platform = str(message.get("platform") or "qq")
            session_id = str(message.get("session_id") or "").strip()
            display_name = str(user_info.get("user_cardname") or user_info.get("user_nickname") or user_id)
            group_info = info.get("group_info") or None
            is_private = group_info is None
            person_id = get_person_id(platform, user_id)
            ts = time.time()

            if is_private:
                self._remember_private(session_id, person_id)
                self._store.touch_message(
                    person_id=person_id, platform=platform, user_id=user_id, display_name=display_name, ts=ts
                )
                self._store.add_event(person_id, "msg_private")
                # 喂感知器：攒消息、按间隔触发 LLM 评估（内部自行频控/防重入）
                self._perceiver.feed_private(session_id, person_id, display_name, text_from_message(message), ts)
            else:
                self._remember_group(session_id, person_id)
                if getattr(self.config.behavior, "track_group", True):
                    self._store.touch_message(
                        person_id=person_id, platform=platform, user_id=user_id, display_name=display_name, ts=ts
                    )
                    group_id = str(group_info.get("group_id") or "")
                    self._store.add_event(person_id, "msg_group", group_id)
                    self._perceiver.feed_group(session_id, person_id, display_name, text_from_message(message), ts)

            self._event_counter += 1
            if self._event_counter >= 500:
                self._event_counter = 0
                self._store.trim_events(int(getattr(self.config.behavior, "max_events", 5000) or 5000))
        except Exception as exc:  # 观察者绝不干扰主流程
            try:
                self.ctx.logger.warning("[关系状态表] on_receive 异常: %s", exc)
            except Exception:
                pass

    # ── 钩子2：麦麦发出消息（私聊回复记一笔"我理过 ta"） ──

    @HookHandler("send_service.after_send", mode=HookMode.OBSERVE)
    async def on_sent(self, message: Optional[Dict[str, Any]] = None, sent: Any = None, **kwargs: Any):
        try:
            if not self._enabled() or sent is not True or not isinstance(message, dict):
                return
            info = message.get("message_info") or {}
            if info.get("group_info"):
                # 群回复也喂给开着回味窗口的人（上下文更完整），但不对特定人记"我理过 ta"
                self._perceiver.feed_bot_group_reply(
                    str(message.get("session_id") or ""), text_from_message(message), time.time()
                )
                return
            session_id = str(message.get("session_id") or "").strip()
            person_id = self._private_sessions.get(session_id)
            if not person_id:
                return
            self._store.touch_bot_reply(person_id, time.time())
            self._store.add_event(person_id, "bot_reply_private")
            # 麦麦的话也进感知器 buffer（评估时上下文更完整）
            self._perceiver.feed_bot_reply(session_id, text_from_message(message), time.time())
        except Exception as exc:
            try:
                self.ctx.logger.warning("[关系状态表] on_sent 异常: %s", exc)
            except Exception:
                pass

    # ── 钩子3：回复前注入关系温度（核心读出口） ──

    @HookHandler("maisaka.replyer.before_request", mode=HookMode.BLOCKING)
    async def on_replyer_request(self, **kwargs: Any):
        try:
            modified = dict(kwargs)
            if not self._enabled():
                return {"action": "continue", "modified_kwargs": modified}
            session_id = str(kwargs.get("session_id") or "").strip()
            if not session_id:
                return {"action": "continue", "modified_kwargs": modified}

            block = ""
            person_id = self._private_sessions.get(session_id)
            if person_id:
                if getattr(self.config.injection, "inject_private", True):
                    row = self._store.get_person(person_id)
                    if row is not None:
                        block = self._build_private_block(row)
            else:
                members = self._group_sessions.get(session_id) or []
                if members and getattr(self.config.injection, "inject_group", True):
                    rows = self._store.get_persons(members)
                    cutoff = time.time() - 86400 * 3  # 只看 3 天内活跃的人
                    rows = [r for r in rows if (r.get("last_msg_at") or 0) >= cutoff]
                    rows.sort(key=lambda r: (r.get("last_msg_at") or 0), reverse=True)
                    max_n = int(getattr(self.config.injection, "group_max_persons", 3) or 3)
                    block = self._build_group_block(rows[: max(1, max_n)])

            # 阶段3a：表达约束 + 今日生活（独立于关系块，即使没有关系数据也注入）
            life = self._life.life_block()
            if life:
                block = (block + "\n" + life) if block else life

            if block:
                base = str(kwargs.get("extra_prompt") or "")
                modified["extra_prompt"] = (base + "\n" + block) if base else block
                if getattr(self.config.injection, "inject_log", False):
                    self.ctx.logger.info("[关系状态表] 已注入 → %s", block.replace("\n", " / ")[:200])
            return {"action": "continue", "modified_kwargs": modified}
        except Exception as exc:  # 注入失败绝不能卡住回复
            try:
                self.ctx.logger.warning("[关系状态表] on_replyer_request 异常: %s", exc)
            except Exception:
                pass
            return {"action": "continue", "modified_kwargs": dict(kwargs)}

    # ── 注入文本 ──

    def _build_private_block(self, row: Dict[str, Any]) -> str:
        name = str(row.get("display_name") or "?")
        uid = str(row.get("user_id") or "")
        aff = float(row.get("affinity") or 0.0)
        mood = float(row.get("mood") or 0.0)
        ign = float(row.get("ignore") or 0.0)
        now = time.time()

        lines = [f"【关系状态·私聊】对象：{name}" + (f"（QQ 尾号 {uid[-4:]}）" if len(uid) >= 4 else "")]
        lines.append(f"- 好感度 {aff:+.0f}/100（{affinity_label(aff)}）")
        # 行为基调：光有数字 LLM 不一定演，按分档给出明确的语气锚点（正值默认热情，不额外加戏）
        if aff <= -60:
            lines.append("- 行为基调：你非常讨厌 ta——回复极简（一两个字也行）、明显不耐烦，能不答就不答，绝不热情，不主动展开任何话题")
        elif aff <= -30:
            lines.append("- 行为基调：你现在不太想理 ta——回复简短敷衍，礼貌但冷，不主动展开话题，对方热络也不要被带热")
        elif aff <= -10:
            lines.append("- 行为基调：你对 ta 有点看不顺眼——语气平淡，偶尔怼一句，保持距离感")
        if mood >= 1:
            lines.append(f"- 今日心情偏移 {mood:+.0f}：今天和 ta 的互动让你心情不错")
        elif mood <= -1:
            lines.append(f"- 今日心情偏移 {mood:+.0f}：今天和 ta 的互动让你有点不快")
        if ign >= 1:
            lines.append(f"- 被冷落指数 {ign:.0f}/100：最近 ta 对你的回应很少，热情自然放低，别过度主动")
        last_msg = float(row.get("last_msg_at") or 0.0)
        last_reply = float(row.get("last_bot_reply_at") or 0.0)
        if last_msg > 0:
            lines.append(f"- 对方最后发言：{fmt_duration(now - last_msg)}")
        if last_reply > 0:
            lines.append(f"- 你上次回复：{fmt_duration(now - last_reply)}")
        total = int(row.get("msg_count_total") or 0)
        if total > 0:
            lines.append(f"- 累计互动约 {total} 条")
        thread_items = self._store.get_active_threads(str(row.get("person_id") or "")) if self._store is not None else []
        if thread_items:
            now2 = time.time()
            parts = []
            for t in thread_items[:3]:  # 最多带 3 条，临期在前
                days_left = max(0, int((float(t["due_at"]) - now2) / 86400))
                due_txt = f"{days_left} 天内" if days_left >= 1 else "就这几天"
                parts.append(f"{t['content']}（{due_txt}适合提起）")
            lines.append(f"- 待续线头：{'；'.join(parts)}")
        # 和解信号（阶段4）：低好感但最近连续态度改善 → 给 planner/语气递台阶，防止冷处理死锁
        if self._store is not None and aff < 0:
            pos, neg = self._store.get_recent_eval_direction(str(row.get("person_id") or ""), 3)
            if pos >= 2 and pos > neg:
                lines.append("- 和解信号：虽然好感还是负的，但 ta 最近几次互动态度明显在改善、也在真诚道歉——你的气其实消得差不多了，语气可以软下来，给个台阶")
        lines.append("（以上仅供你参考调整语气，绝对不要向对方提及这些数据的存在）")
        return "\n".join(lines)

    def _build_group_block(self, rows: List[Dict[str, Any]]) -> str:
        if not rows:
            return ""
        now = time.time()
        lines = ["【关系状态·群聊】最近和你互动的群友（参考）："]
        for r in rows:
            name = str(r.get("display_name") or "?")
            aff = float(r.get("affinity") or 0.0)
            mood = float(r.get("mood") or 0.0)
            ign = float(r.get("ignore") or 0.0)
            last = float(r.get("last_msg_at") or 0.0)
            line = f"- {name}：好感 {aff:+.0f}（{affinity_label(aff)}）"
            if abs(mood) >= 1:
                line += f"｜心情 {mood:+.0f}"
            if ign >= 1:
                line += f"｜冷落 {ign:.0f}"
            if last > 0:
                line += f"｜最后发言 {fmt_duration(now - last)}"
            lines.append(line)
        lines.append("（供你把握对每个人的态度，绝对不要向群里提及这些数据的存在）")
        return "\n".join(lines)

    # ── 命令 ──

    # 正则要点（官方陷阱清单 §13-7）：宿主用 re.search 匹配，回复场景下命令不在文本开头，
    # `^` 锚点会失配 → 用 (?<!\S) 负向前瞻（命令前必须是行首或空白）代替 ^。
    @Command("关系", description="查看关系状态：/关系 或 /关系 <QQ号|昵称>", pattern=r"(?<!\S)/关系(?:\s+(?P<target>.+?))?\s*$")
    async def cmd_relation(self, stream_id: str = "", matched_groups: Optional[Dict[str, Any]] = None, **kwargs: Any):
        try:
            groups = matched_groups or {}
            target = str(groups.get("target") or "").strip()
            text = self._render_query(stream_id, target)
        except Exception as exc:
            text = f"❌ 查询出错：{exc}"
        await self.ctx.send.text(text, stream_id)
        return True, "ok", True

    @Command(
        "ss_set",
        description="管理：/ss_set <QQ号> <字段> <值>（thread 可加 #天数，如 ...#1；仅操作员）",
        pattern=r"(?<!\S)/ss_set\s+(?P<person>\S+)\s+(?P<field>\S+)\s+(?P<value>.+?)\s*$",
        permission="operator",
    )
    async def cmd_set(self, stream_id: str = "", matched_groups: Optional[Dict[str, Any]] = None, **kwargs: Any):
        try:
            if not self._enabled():
                text = "⚠️ 插件未启用或存储未就绪"
            else:
                groups = matched_groups or {}
                qq = str(groups.get("person") or "").strip()
                field = str(groups.get("field") or "").strip()
                value = str(groups.get("value") or "").strip()
                days = None
                if field == "thread":
                    import re as _re
                    m_days = _re.search(r"#(\d{1,2})$", value)
                    if m_days:
                        days = float(m_days.group(1))
                        value = value[: m_days.start()].strip()
                store = self._store
                assert store is not None
                # 按 QQ 号找（找不到再按昵称）
                target = store.find_person(qq)
                person_id = target["person_id"] if target else get_person_id("qq", qq)
                ok, msg = store.set_field(person_id, field, value, days)
                text = msg
        except Exception as exc:
            text = f"❌ 设置出错：{exc}"
        await self.ctx.send.text(text, stream_id)
        return True, "ok", True

    @Command("今天", description="查看麦麦今天的日程", pattern=r"(?<!\S)/今天\s*$")
    async def cmd_today(self, stream_id: str = "", matched_groups: Optional[Dict[str, Any]] = None, **kwargs: Any):
        try:
            if not self._enabled() or not bool(getattr(getattr(self.config, "daily_life", None), "enabled", True)):
                text = "⚠️ 生活日程未启用"
            else:
                date = time.strftime("%Y-%m-%d")
                assert self._store is not None
                items = self._store.get_schedule(date)
                if not items:
                    self._life._ensure_generate(date)
                    text = "今天的日程还在排，稍等几分钟再 /今天 看看"
                else:
                    dcfg = getattr(self.config, "daily_life", None)
                    wake = int(clamp(getattr(dcfg, "wake_hour", 8), 5, 12))
                    sleep = int(clamp(getattr(dcfg, "sleep_hour", 23), 21, 28))
                    bed = sleep if sleep <= 24 else sleep - 24
                    lines = [f"📅 麦麦今天（{date}）的日程："]
                    for it in items:
                        lines.append(f"  {it['period']}  {it['content']}")
                    hour_now = time.localtime().tm_hour
                    now_state = self._life.night_state(hour_now) or self._life.current_activity(items, hour_now) or "自由时间"
                    lines.append(f"（{wake:02d} 点起床，{bed:02d} 点睡；现在这个点：{now_state}）")
                    text = "\n".join(lines)
        except Exception as exc:
            text = f"❌ 查询出错：{exc}"
        await self.ctx.send.text(text, stream_id)
        return True, "ok", True

    @Command("关系帮助", description="关系状态表使用帮助", pattern=r"(?<!\S)/关系帮助\s*$")
    async def cmd_help(self, stream_id: str = "", matched_groups: Optional[Dict[str, Any]] = None, **kwargs: Any):
        text = (
            "💞 关系状态表（阶段1 地基）\n"
            "给每个联系人记一本账：好感度 / 今日心情 / 被冷落指数 / 待续线头 / 互动时间。\n"
            "麦麦回复时会自动参考（对喜欢的人更热情，被冷落时更克制）。\n\n"
            "命令：\n"
            "  /关系 —— 私聊查自己；群里看最近互动 top5\n"
            "  /关系 <QQ号或昵称> —— 查指定的人\n"
            "  /今天 —— 看麦麦今天的日程\n"
            "  /ss_set <QQ号> <字段> <值> —— 手动调账（仅操作员）\n"
            "     字段：affinity 好感(-100~100)｜mood 心情(-50~50)｜ignore 冷落(0~100)｜thread 线头\n"
            "     例：/ss_set 123456 affinity 30 ；/ss_set 123456 thread 周末约了漫展\n"
            "  /关系帮助 —— 本说明\n\n"
            "说明：好感/心情由感知器自动打分（LLM 语境化评估，每轮对话按间隔评估一次），\n"
            "也可用 /ss_set 手动校准。心情隔天自动归零，冷落指数每天缓解，线头默认 10 天有效。\n"
            "麦麦每天有自己的日程（问\"在干嘛\"能答出正在干嘛），数据在 data/plugins/social_state/ 下。"
        )
        await self.ctx.send.text(text, stream_id)
        return True, "ok", True

    def _render_query(self, stream_id: str, target: str) -> str:
        store = self._store
        if store is None:
            return "⚠️ 插件未启用或存储未就绪"

        if target:
            row = store.find_person(target)
            if row is None:
                return f"没找到「{target}」——ta 还没和麦麦说过话，或昵称对不上（可用 QQ 号试试）"
            return self._render_row(row)

        person_id = self._private_sessions.get(stream_id)
        if person_id:
            row = store.get_person(person_id)
            if row is not None:
                return self._render_row(row)

        # 群里：最近互动 top5
        rows = store.top_persons(5)
        if not rows:
            return "还没有任何记录——先让麦麦跟人聊几句吧"
        lines = ["💞 最近互动的关系状态（top5）："]
        for row in rows:
            lines.append(self._render_row(row, compact=True))
        return "\n".join(lines)

    def _render_row(self, row: Dict[str, Any], compact: bool = False) -> str:
        name = str(row.get("display_name") or "?")
        uid = str(row.get("user_id") or "")
        aff = float(row.get("affinity") or 0.0)
        mood = float(row.get("mood") or 0.0)
        ign = float(row.get("ignore") or 0.0)
        now = time.time()
        last_msg = float(row.get("last_msg_at") or 0.0)
        last_reply = float(row.get("last_bot_reply_at") or 0.0)
        total = int(row.get("msg_count_total") or 0)

        if compact:
            line = f"• {name}" + (f"({uid})" if uid else "") + f"：好感 {aff:+.0f}（{affinity_label(aff)}）"
            if abs(mood) >= 1:
                line += f"｜心情 {mood:+.0f}"
            if ign >= 1:
                line += f"｜冷落 {ign:.0f}"
            if last_msg > 0:
                line += f"｜发言 {fmt_duration(now - last_msg)}"
            return line

        lines = [
            f"💞 {name}" + (f"（QQ {uid}）" if uid else ""),
            f"好感：{aff:+.0f}/100（{affinity_label(aff)}）",
            f"心情偏移：{mood:+.0f}｜冷落：{ign:.0f}/100",
        ]
        if last_msg > 0:
            lines.append(f"对方最后发言：{fmt_duration(now - last_msg)}")
        if last_reply > 0:
            lines.append(f"麦麦上次回复：{fmt_duration(now - last_reply)}")
        if total > 0:
            lines.append(f"累计互动约 {total} 条")
        thread_items = self._store.get_active_threads(str(row.get("person_id") or "")) if self._store is not None else []
        if thread_items:
            now2 = time.time()
            t_parts = []
            for t in thread_items[:3]:
                days_left = max(0, int((float(t["due_at"]) - now2) / 86400))
                t_parts.append(f"{t['content']}（剩 {days_left} 天）")
            lines.append(f"待续线头：{'；'.join(t_parts)}")
        return "\n".join(lines)


def create_plugin() -> SocialStatePlugin:
    return SocialStatePlugin()
