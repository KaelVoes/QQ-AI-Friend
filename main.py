# =============================================================================
# 李欣然 · QQ 聊天机器人（修复版：禁止反问代替回答）
# =============================================================================
import asyncio
import websockets
import json
import requests
import re
import time
import random
import os
import base64
import datetime
import urllib.request
import urllib.parse
from zoneinfo import ZoneInfo

# =============================================================================
# 【0】配置文件加载
# =============================================================================
CONFIG = {}
try:
    with open("data/config.json", "r", encoding="utf-8") as f:
        CONFIG = json.load(f)
    print("✅ 配置已加载：config.json")
except Exception as e:
    print(f"⚠️ 配置文件加载失败，使用默认值：{e}")
    CONFIG = {}

# =============================================================================
# 【1】配置区
# =============================================================================
WS_URL = "ws://127.0.0.1:3001/?access_token=123456"
OLLAMA_URL = "http://127.0.0.1:11434/api/chat"
MODEL_NAME = "qwen3:8b"
MASTER_QQ = 0  # 改成你的QQ号
DEFAULT_CITY = "上海"  # 改成你的城市

BOT_TIMEZONE = "Asia/Shanghai"
TIMEZONE_SYNC_INTERVAL = 1800

PROACTIVE_INTERVAL = CONFIG.get("proactive", {}).get("interval_check", 60)
PROACTIVE_COOLDOWN_MIN = 3600
PROACTIVE_COOLDOWN_MAX = 14400
ACTIVE_HOUR_START = 8
ACTIVE_HOUR_END = 23

ENABLE_NUISANCE = True
NUISANCE_CHECK_INTERVAL = CONFIG.get("nuisance", {}).get("check_interval", 60)
NUISANCE_CHANCE_PER_CHECK = CONFIG.get("nuisance", {}).get("chance_per_check", 0.08)
NUISANCE_COOLDOWN_MIN = 600
NUISANCE_COOLDOWN_MAX = 3600
NUISANCE_MAX_LEN = 15

LATE_NIGHT_CHANCE = 0.4
LATE_NIGHT_START_MIN = 1
LATE_NIGHT_START_MAX = 3

MAX_HISTORY_LEN = CONFIG.get("chat", {}).get("max_history_len", 40)
MAX_MEMORY_ITEMS = 10

EVENTS_FILE = "data/events.json"
MEMORY_FILE = "data/memory.json"
COURSES_FILE = "data/courses.json"
WALLET_FILE = "data/wallet.json"
HISTORY_FILE = "data/history.json"
HOLIDAYS_FILE = "data/holidays.json"
CHAT_HISTORY_FILE = "data/chat_history.json"
CHAT_HISTORY_SAVE_MAX = 20
CHAT_HISTORY_ARCHIVE_DIR = "data/chat_archive"  # 按天归档的目录
ENABLE_COURSE = True

EVENT_TTL_HOURS = 9
EVENT_POOL_MAX = 30
EVENT_APPEND_CHANCE = 0.5
EVENT_APPEND_MIN = 1
EVENT_APPEND_MAX = 2

HISTORY_TTL_DAYS = 7
WORLD_TICK_INTERVAL = 60

ENABLE_SLEEP = True
SLEEP_START_HOUR = 23
SLEEP_END_HOUR = 7

WAKE_UP_BASE_CHANCE = 0.25
WAKE_UP_NEAR_MORNING_BONUS = 0.40
WAKE_UP_REPEAT_BONUS = 0.20
WAKE_UP_MAX_CHANCE = 0.95
WAKE_UP_FORCE_AFTER = 5
WAKE_UP_RESET_MINUTES = 30

AWAKE_WINDOW_MINUTES = 15
AWAKE_START_CHANCE = 0.90
AWAKE_END_CHANCE = 0.35

FATIGUE_INIT = CONFIG.get("fatigue", {}).get("init", 20)
FATIGUE_MAX = 100
FATIGUE_BASE_RATE = 3
FATIGUE_LATE_NIGHT_RATE = 8
FATIGUE_AFTERNOON_RATE = 5
FATIGUE_SLEEP_RECOVER = 12
FATIGUE_WAKEUP_PENALTY = 8

MONTHLY_INCOME = CONFIG.get("wallet", {}).get("monthly_income", 2500)
DAILY_BREAKFAST = (6, 12)
DAILY_LUNCH = (15, 30)
DAILY_DINNER = (15, 30)
DAILY_RANDOM_COUNT = (0, 3)
MONTHLY_BIG_CHANCE = 0.10

BOT_BIRTHDAY_MONTH = 9
BOT_BIRTHDAY_DAY = 20

DAILY_RANDOM_ITEMS = [
    "奶茶：三分糖", "水果", "打印课件", "快递费",
    "零食", "日用品", "食堂加餐", "饮料",
    "洗衣服", "水果茶",
]

MONTHLY_BIG_ITEMS = [
    ("买了本书", 30, 100),
    ("买了件衣服", 100, 500),
    ("和室友聚餐", 50, 150),
    ("看电影", 40, 80),
    ("买美妆", 50, 200),
    ("买鞋", 200, 600),
    ("给妈妈买礼物", 80, 300),
    ("和同学 KTV", 60, 150),
]

DEFAULT_BOT_FIXED = [
    "名字：李欣然",
    "年龄：20 岁",
    "生日：9 月 20 日",
    "身份：上海某大学大二学生",
    "专业：新闻传播",
    "家乡：苏州",
    "城市：上海",
    "室友：小美（睡上铺）、阿静（对床）",
]

DEFAULT_BOT_DYNAMIC = [
    ("喜欢的食物：生煎、小笼包、奶茶（三分糖）、火锅", 180),
    ("讨厌的东西：早起、跑步、虫子", 365),
    ("常去的地方：武康路、外滩、梧桐区、图书馆", 180),
    ("习惯：每天必喝咖啡、睡前刷手机", 90),
    ("近期：期中考试周快到了，在死磕传播学概论", 7),
    ("近期心情：有点小焦虑", 3),
]

# =============================================================================
# 【2】全局变量
# =============================================================================
chat_histories = {}
last_interaction_time = {}
long_term_memory = {}
_event_pool = []
_active_effects = []  # [{text, start_ts, duration_sec, fatigue_rate_mod}]

# 待回复队列
pending_reason = None
pending_replies = []
_birthday_mention_count = 0  # 今天提了几次生日
_birthday_mention_date = ""  # 上次提生日的日期
_sleep_message_state = {"count": 0, "last_ts": 0}
_wake_state = None
_wakeup_count_per_night = {}
fatigue = FATIGUE_INIT
_last_fatigue_update = 0
affinity = {}  # {user_id: 亲密度 0-100}
bot_fixed_memory = list(DEFAULT_BOT_FIXED)
bot_dynamic_memory = []
COURSE_SCHEDULE = {}
_course_note_cache = {}
wallet = {}
_world_history = []
_world_tick_state = {"today_date": "", "today_points": []}
_purchases = []  # 购物记录
_consumables = []  # 消耗品耐久
_knowledge = {}  # 知识增长系统
_period_state = {"last_period": "", "cycle_days": 28, "period_length": 5}  # 生理期
_weight = 48.0  # 体重（kg）
_first_chat_date = {}  # {user_id: "2026-09-20"} 认识天数
_internship_state = {"year": 0, "doing": False}  # 实习状态
_holidays = {}
_late_night_flag = {}
_next_proactive_time = 0
_next_nuisance_time = 0

# =============================================================================
# 【3】现实时间中枢
# =============================================================================
_dynamic_timezone = None
_last_tz_location = None

def _get_timezone_str():
    return _dynamic_timezone or BOT_TIMEZONE

def _now():
    try:
        return datetime.datetime.now(ZoneInfo(_get_timezone_str()))
    except Exception:
        return datetime.datetime.now()

def _now_ts():
    return time.time()

def _today_str():
    return _now().strftime("%Y-%m-%d")

def _month_str():
    return _now().strftime("%Y-%m")

def _current_hour():
    return _now().hour

def _current_minute():
    return _now().minute

def _today_ts_at(h, m):
    n = _now()
    dt = n.replace(hour=h, minute=m, second=0, microsecond=0)
    return dt.timestamp()

def is_birthday():
    n = _now()
    return n.month == BOT_BIRTHDAY_MONTH and n.day == BOT_BIRTHDAY_DAY

def is_late_night_tonight():
    return _late_night_flag.get(_today_str(), False)

# =============================================================================
# 【4】节假日系统
# =============================================================================
def load_holidays():
    global _holidays
    _holidays = {}
    try:
        with open(HOLIDAYS_FILE, "r", encoding="utf-8") as f:
            _holidays = json.load(f)
        fixed = len(_holidays.get("fixed_holidays", []))
        lunar = len(_holidays.get("lunar_holidays", []))
        print(f"🎉 已加载节假日：公历 {fixed} 条，农历/按年 {lunar} 条")
    except FileNotFoundError:
        print(f"⚠️ 找不到 {HOLIDAYS_FILE}，节假日系统停用")
        _holidays = {}
    except Exception as e:
        print(f"⚠️ 加载节假日失败: {e}")
        _holidays = {}

# =============================================================================
# 【4.5】对话历史持久化
# =============================================================================
def load_chat_history():
    global chat_histories
    if not os.path.exists(CHAT_HISTORY_FILE):
        print(f"💬 未找到 {CHAT_HISTORY_FILE}，将新建")
        return
    try:
        with open(CHAT_HISTORY_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        count = 0
        for uid_str, messages in data.items():
            uid = int(uid_str)
            # 拼上 system prompt + few-shot + 保存的对话
            chat_histories[uid] = [{"role": "system", "content": SYSTEM_PROMPT}] + FEW_SHOT_EXAMPLES + messages
            count += len(messages)
        print(f"💬 已加载对话历史：{len(data)} 个用户，共 {count} 条消息")
    except Exception as e:
        print(f"⚠️ 加载对话历史失败: {e}")

def save_chat_history():
    try:
        # 归档：把今天的对话按天存
        import os
        archive_dir = os.path.join(os.path.dirname(__file__), CHAT_HISTORY_ARCHIVE_DIR)
        os.makedirs(archive_dir, exist_ok=True)
        today_str = _today_str()
        archive_file = os.path.join(archive_dir, f"chat_{today_str}.json")

        # 加载今天的归档
        today_archive = {}
        if os.path.exists(archive_file):
            try:
                with open(archive_file, "r", encoding="utf-8") as f:
                    today_archive = json.load(f)
            except:
                today_archive = {}

        # 把当前对话合并到今天的归档
        data = {}
        few_shot_count = len(FEW_SHOT_EXAMPLES)
        for uid, messages in chat_histories.items():
            # 结构：[system] + few-shot + 真实对话，跳过前 few_shot_count+1 条
            real_messages = messages[1 + few_shot_count:]
            saved = []
            for m in real_messages:
                if m["role"] not in ("user", "assistant"):
                    continue
                entry = {"role": m["role"]}
                # user 消息里可能带了内心参考前缀，只保留用户真正说的话
                if m["role"] == "user":
                    text = m["content"]
                    # 去掉 "（内心参考，勿复述：...）" 前缀
                    idx = text.find("）\n")
                    if idx != -1 and text.startswith("（内心参考"):
                        entry["content"] = text[idx + 2:]
                    else:
                        entry["content"] = text
                else:
                    entry["content"] = m["content"]
                saved.append(entry)
            # 限制保存条数
            if len(saved) > CHAT_HISTORY_SAVE_MAX:
                saved = saved[-CHAT_HISTORY_SAVE_MAX:]
            data[str(uid)] = saved
        # 合并到今天的归档（不限制条数）
        for uid, entries in data.items():
            if uid not in today_archive:
                today_archive[uid] = []
            # 追加新的（去重）
            existing_contents = {e["content"] for e in today_archive[uid]}
            for e in entries:
                if e["content"] not in existing_contents:
                    today_archive[uid].append(e)

        # 保存归档
        with open(archive_file, "w", encoding="utf-8") as f:
            json.dump(today_archive, f, ensure_ascii=False, indent=2)

        # 保存当前对话（只保留最近20条）
        with open(CHAT_HISTORY_FILE, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except Exception as e:
        print(f"保存对话历史失败: {e}")

_api_holidays = {}  # API获取的节假日数据

def fetch_holidays_from_api(year=None):
    """从API获取当年节假日（多源备用）"""
    if not year:
        year = _now().year

    # 源1: timor.tech
    try:
        url = f"https://timor.tech/api/holiday/year/{year}"
        resp = requests.get(url, timeout=5)
        data = resp.json()
        if data.get("code") == 0:
            holidays = data.get("holiday", {})
            result = {}
            for date_str, info in holidays.items():
                result[date_str] = {
                    "name": info.get("name", "节日"),
                    "holiday": info.get("holiday", True),
                }
            print(f"📅 API获取 {year} 年节假日 {len(result)} 天（源1）")
            return result
    except Exception as e:
        print(f"⚠️ 源1失败: {e}")

    # 源2: jiejiariapi
    try:
        url = f"https://api.jiejiariapi.com/v1/holidays/{year}"
        resp = requests.get(url, timeout=5)
        data = resp.json()
        result = {}
        for date_str, info in data.items():
            result[date_str] = {
                "name": info.get("name", "节日"),
                "holiday": info.get("holiday", True),
            }
        print(f"📅 API获取 {year} 年节假日 {len(result)} 天（源2）")
        return result
    except Exception as e:
        print(f"⚠️ 源2失败: {e}")

    print(f"⚠️ 所有节假日API都失败，使用本地写死的")
    return {}

def get_today_holiday():
    today = _now().date()
    today_str = today.strftime("%Y-%m-%d")

    # 1. 先查API获取的真实节假日
    if today_str in _api_holidays:
        info = _api_holidays[today_str]
        if info["holiday"]:  # 放假的日子
            # 估算放假天数和第几天
            day_index = 1
            days = 1
            for i in range(1, 15):
                check = (today + datetime.timedelta(days=i)).strftime("%Y-%m-%d")
                if check in _api_holidays and _api_holidays[check]["holiday"]:
                    days += 1
                else:
                    break
            return {
                "name": info["name"],
                "mood": 2,
                "note": f"放假：{info['name']}",
                "_day_index": day_index,
            }

    # 2. 再查本地写死的节假日（API没覆盖的）
    if not _holidays:
        return None

    for h in _holidays.get("fixed_holidays", []):
        try:
            days = h.get("days", 1)
            for year_offset in (0, -1):
                year = today.year + year_offset
                start = datetime.datetime.strptime(f"{year}-{h['date']}", "%Y-%m-%d").date()
                end = start + datetime.timedelta(days=days)
                if start <= today < end:
                    h = dict(h)
                    h["_start"] = start
                    h["_end"] = end
                    h["_day_index"] = (today - start).days + 1
                    return h
        except Exception:
            continue

    for h in _holidays.get("lunar_holidays", []):
        try:
            days = h.get("days", 1)
            start = datetime.datetime.strptime(h["date"], "%Y-%m-%d").date()
            end = start + datetime.timedelta(days=days)
            if start <= today < end:
                h = dict(h)
                h["_start"] = start
                h["_end"] = end
                h["_day_index"] = (today - start).days + 1
                return h
        except Exception:
            continue

    return None

# =============================================================================
# 【5】睡觉机制（含熬夜）
# =============================================================================
_sleep_schedule_cache = {}

def _get_sleep_hours_today():
    today = _today_str()
    if today not in _sleep_schedule_cache:
        _sleep_schedule_cache.clear()
        _late_night_flag.clear()

        # 熬夜概率受多种因素影响
        chance = LATE_NIGHT_CHANCE

        # 周末更容易熬夜
        weekday = _now().weekday()
        if weekday >= 5:
            chance += 0.15

        # 明天没课更容易熬夜
        tomorrow = _now() + datetime.timedelta(days=1)
        tomorrow_str = str(tomorrow.isoweekday())
        if not COURSE_SCHEDULE.get(tomorrow_str):
            chance += 0.2

        # 疲劳很高反而困，不想熬夜
        _, _, fatigue_val = get_fatigue_modifier()
        if fatigue_val > 70:
            chance -= 0.2
        elif fatigue_val < 30:
            chance += 0.1  # 精力充沛更容易熬夜

        chance = max(0.05, min(0.8, chance))  # 5%~80%之间

        if random.random() < chance:
            start = random.randint(LATE_NIGHT_START_MIN, LATE_NIGHT_START_MAX)
            _late_night_flag[today] = True
            print(f"🌙 今晚决定熬夜，{start} 点才睡（概率 {chance:.0%}）")
        else:
            start = SLEEP_START_HOUR + random.choice([-1, 0, 0, 0, 1])
            start = max(21, min(23, start))
            _late_night_flag[today] = False

        # 起床时间受明天课程/周末影响
        tomorrow = _now() + datetime.timedelta(days=1)
        tomorrow_str = str(tomorrow.isoweekday())
        tomorrow_courses = COURSE_SCHEDULE.get(tomorrow_str, [])

        if tomorrow_courses:
            # 明天有课，找最早的那节课几点
            earliest = min(int(c["start"].split(":")[0]) for c in tomorrow_courses)
            # 起床时间 = 最早课之前1.5小时
            end = earliest - 1.5 + random.uniform(-0.5, 0.5)
            end = max(6, min(10, int(end)))
        else:
            # 明天没课，睡懒觉
            weekday = tomorrow.weekday()
            if weekday >= 5:
                end = random.randint(9, 11)  # 周末睡到9-11点
            else:
                end = random.randint(8, 10)  # 工作日没课睡到8-10点

        _sleep_schedule_cache[today] = (start, end)
        print(f"😴 今日睡眠（{_get_timezone_str()}）：{start}:00 - {end}:00（明天有{len(tomorrow_courses)}节课）")
    return _sleep_schedule_cache[today]

def is_sleeping():
    if not ENABLE_SLEEP:
        return False
    hour = _current_hour()
    start, end = _get_sleep_hours_today()

    # 疲劳值越高，实际睡觉时间越提前
    if fatigue > 85:
        actual_start = start - 3  # 提前3小时
    elif fatigue > 70:
        actual_start = start - 2  # 提前2小时
    elif fatigue > 50:
        actual_start = start - 1  # 提前1小时
    else:
        actual_start = start

    # 实际睡觉时间段
    if actual_start >= end:
        in_sleep = hour >= actual_start or hour < end
    else:
        in_sleep = actual_start <= hour < end

    return in_sleep

def _get_awake_window_minutes():
    """根据疲劳值计算半清醒窗口：越累越快又睡着"""
    update_fatigue()
    # 疲劳0: 22分钟, 疲劳50: 15分钟, 疲劳100: 8分钟
    return max(5, AWAKE_WINDOW_MINUTES * (1.5 - fatigue / 100))

def get_awake_state():
    global _wake_state
    if not _wake_state:
        return None
    elapsed_min = (_now_ts() - _wake_state["wake_ts"]) / 60
    window = _get_awake_window_minutes()
    if elapsed_min > window:
        _wake_state = None
        return None
    return _wake_state

def record_wakeup_event():
    today = _today_str()
    count = _wakeup_count_per_night.get(today, 0) + 1
    _wakeup_count_per_night[today] = count

    for k in list(_wakeup_count_per_night.keys()):
        if k != today:
            del _wakeup_count_per_night[k]

    if count == 1:
        text = "昨晚被消息吵醒，没睡好"
        score = -2
    elif count <= 3:
        text = f"半夜被吵醒 {count} 次，睡得很差"
        score = -3
    else:
        text = f"半夜被吵醒 {count} 次，几乎没睡好"
        score = -4

    existing = None
    for e in _event_pool:
        if e.get("tag") == "wakeup":
            existing = e
            break

    if existing:
        existing["text"] = text
        existing["score"] = score
        existing["ts"] = _now_ts()
    else:
        _event_pool.append({
            "text": text,
            "score": score,
            "ts": _now_ts(),
            "tag": "wakeup",
        })

    _world_history.append({
        "ts": _now_ts(),
        "date": today,
        "time": _now().strftime("%H:%M"),
        "type": "wakeup",
        "desc": f"被消息吵醒（第 {count} 次）",
        "amount": 0,
    })
    save_history()
    save_memory()
    print(f"📝 记录被吵醒事件：{text}（{score:+d}分，第 {count} 次）")

def mark_awake():
    global _wake_state
    if _wake_state:
        _wake_state["wake_ts"] = _now_ts()
        _wake_state["repeat_count"] = _wake_state.get("repeat_count", 0) + 1
    else:
        _wake_state = {
            "wake_ts": _now_ts(),
            "repeat_count": 0,
        }
        record_wakeup_event()
        add_fatigue(FATIGUE_WAKEUP_PENALTY)
        window = _get_awake_window_minutes()
        print(f"☕ 进入半清醒窗口（约{window:.0f} 分钟），疲劳 +{FATIGUE_WAKEUP_PENALTY}")

def should_wake_up():
    global _sleep_message_state
    if not is_sleeping():
        return True

    awake = get_awake_state()
    if awake:
        elapsed_min = (_now_ts() - awake["wake_ts"]) / 60
        window = _get_awake_window_minutes()
        progress = min(elapsed_min / window, 1.0)
        chance = AWAKE_START_CHANCE - progress * (AWAKE_START_CHANCE - AWAKE_END_CHANCE)
        repeat = awake.get("repeat_count", 0)
        chance += repeat * 0.05
        chance = min(chance, 0.98)
        print(f"☕ 半清醒中（已醒 {elapsed_min:.1f} 分钟），回复概率 {chance:.2f}")
        return random.random() < chance

    now_ts = _now_ts()
    state = _sleep_message_state

    if now_ts - state["last_ts"] > WAKE_UP_RESET_MINUTES * 60:
        state["count"] = 0

    state["count"] += 1
    state["last_ts"] = now_ts

    if state["count"] >= WAKE_UP_FORCE_AFTER:
        print(f"😴 连续 {state['count']} 条未回，强制吵醒")
        return True

    chance = WAKE_UP_BASE_CHANCE
    hour = _current_hour()
    _, end = _get_sleep_hours_today()
    hours_to_wake = (end - hour) % 24
    if hours_to_wake <= 1:
        chance += WAKE_UP_NEAR_MORNING_BONUS
    elif hours_to_wake <= 2:
        chance += WAKE_UP_NEAR_MORNING_BONUS * 0.5

    chance += (state["count"] - 1) * WAKE_UP_REPEAT_BONUS
    chance = min(chance, WAKE_UP_MAX_CHANCE)

    print(f"😴 睡眠中，被吵醒概率 {chance:.2f}（第 {state['count']} 条消息）")
    return random.random() < chance

def _clear_sleep_state():
    global _sleep_message_state
    _sleep_message_state = {"count": 0, "last_ts": 0}

# =============================================================================
# 【6】疲劳系统
# =============================================================================
def update_fatigue():
    global fatigue, _last_fatigue_update
    now = _now_ts()
    if _last_fatigue_update == 0:
        _last_fatigue_update = now
        return

    elapsed = now - _last_fatigue_update
    if elapsed < 60:
        return

    hours = elapsed / 3600.0

    if is_sleeping():
        recover = FATIGUE_SLEEP_RECOVER * hours
        fatigue = max(0, fatigue - recover)
    else:
        hour = _current_hour()
        if 23 <= hour or hour < 2:
            rate = FATIGUE_LATE_NIGHT_RATE
        elif 14 <= hour < 16:
            rate = FATIGUE_AFTERNOON_RATE
        else:
            rate = FATIGUE_BASE_RATE

        # 叠加激活效果的修正
        rate_mod = _get_fatigue_rate_mod()
        rate = max(0, rate + rate_mod)

        fatigue = min(FATIGUE_MAX, fatigue + rate * hours)

    _last_fatigue_update = now

def get_fatigue_modifier():
    update_fatigue()
    f = fatigue

    if f < 20:
        return "精神饱满", +2, f
    elif f < 40:
        return "状态还行", +1, f
    elif f < 60:
        return "有点累", 0, f
    elif f < 80:
        return "很累", -1, f
    else:
        return "快撑不住了", -3, f

def add_fatigue(amount):
    global fatigue, _last_fatigue_update
    fatigue = min(FATIGUE_MAX, fatigue + amount)
    _last_fatigue_update = _now_ts()

# =============================================================================
# 【7】钱包系统
# =============================================================================
def _init_wallet_default():
    return {
        "month": "",
        "monthly_income": MONTHLY_INCOME,
        "balance": MONTHLY_INCOME,
        "month_big_spent": False,
    }

def load_wallet():
    global wallet
    if not os.path.exists(WALLET_FILE):
        wallet = _init_wallet_default()
        wallet["month"] = _month_str()
        save_wallet()
        print(f"💰 新建钱包：{MONTHLY_INCOME} 元")
        return
    try:
        with open(WALLET_FILE, "r", encoding="utf-8") as f:
            wallet = json.load(f)
        print(f"💰 已加载钱包：余额 {wallet.get('balance', 0):.2f} 元")
    except Exception as e:
        print(f"⚠️ 加载钱包失败: {e}")
        wallet = _init_wallet_default()

def save_wallet():
    try:
        with open(WALLET_FILE, "w", encoding="utf-8") as f:
            json.dump(wallet, f, ensure_ascii=False, indent=2)
    except Exception as e:
        print(f"保存钱包失败: {e}")

def _maybe_reset_monthly():
    cur_month = _month_str()
    if wallet.get("month") != cur_month:
        wallet["month"] = cur_month
        wallet["balance"] = MONTHLY_INCOME
        wallet["monthly_income"] = MONTHLY_INCOME
        wallet["month_big_spent"] = False
        save_wallet()
        print(f"💰 新月到账：{MONTHLY_INCOME} 元")

def get_wallet_modifier():
    _maybe_reset_monthly()
    income = wallet.get("monthly_income", MONTHLY_INCOME) or MONTHLY_INCOME
    balance = wallet.get("balance", 0)
    ratio = balance / income if income > 0 else 0

    if ratio >= 0.6:
        return "手头宽裕", +1, ratio
    elif ratio >= 0.3:
        return "正常", 0, ratio
    elif ratio >= 0.15:
        return "开始省着花", -1, ratio
    else:
        return "月底吃土", -2, ratio

def get_wallet_str():
    balance = wallet.get("balance", 0)
    income = wallet.get("monthly_income", MONTHLY_INCOME)
    today = _today_str()

    today_spent_items = [
        e for e in _world_history
        if e.get("date") == today and e.get("amount", 0) > 0
    ]
    today_spent = sum(e["amount"] for e in today_spent_items)
    items_desc = "、".join(f"{e['desc']} {e['amount']}元" for e in today_spent_items[:6]) or "无"

    s = (
        f"本月预算 {income:.0f} 元，还剩 {balance:.1f} 元，"
        f"今天已花 {today_spent:.1f} 元；今日开销：{items_desc}"
    )
    return s

def is_exam_week():
    """现在是不是考试周"""
    month = _now().month
    # 期中：4月中下旬、11月中下旬
    # 期末：6月底、1月初
    day = _now().day
    if (month == 4 and day >= 15) or (month == 11 and day >= 15):
        return True, "midterm"
    if (month == 6 and day >= 20) or (month == 1 and day <= 15):
        return True, "final"
    return False, ""

def is_internship():
    """现在是不是在实习"""
    month = _now().month
    year = _now().year

    # 不是暑假就不实习
    if month not in (7, 8):
        return False

    # 新的一年，重新决定要不要实习
    if _internship_state.get("year") != year:
        _internship_state["year"] = year
        # 大二暑假有50%概率去实习
        _internship_state["doing"] = random.random() < 0.5
        print(f"💼 {year}年暑假：{'去实习了' if _internship_state['doing'] else '没去实习，在家躺平'}")
        save_history()

    return _internship_state.get("doing", False)

def get_days_known(user_id):
    """认识多少天"""
    if user_id not in _first_chat_date:
        return 0
    try:
        first = datetime.datetime.strptime(_first_chat_date[user_id], "%Y-%m-%d").date()
        today = _now().date()
        return (today - first).days
    except:
        return 0

def is_on_period():
    """现在是不是生理期"""
    if not _period_state.get("last_period"):
        # 第一次用，随机设定一个日期
        today = _now().date()
        random_day = random.randint(1, 28)
        from datetime import timedelta
        last = today - timedelta(days=random_day)
        _period_state["last_period"] = last.strftime("%Y-%m-%d")
        save_history()

    last = datetime.datetime.strptime(_period_state["last_period"], "%Y-%m-%d").date()
    cycle_days = _period_state.get("cycle_days", 28)
    period_length = _period_state.get("period_length", 5)
    today = _now().date()
    days_since = (today - last).days

    # 每 cycle_days 天来一次，每次持续 period_length 天
    if days_since % cycle_days < period_length:
        return True
    return False

def get_period_mood_effect():
    """生理期对心情的影响"""
    if not is_on_period():
        return 0, ""
    return -2, "生理期，肚子有点不舒服，想吃甜的"

def get_season():
    """根据月份返回季节"""
    month = _now().month
    if month in (3, 4, 5):
        return "spring"
    elif month in (6, 7, 8):
        return "summer"
    elif month in (9, 10, 11):
        return "autumn"
    else:
        return "winter"

def get_season_mood_effect():
    """季节对心情的影响"""
    season = get_season()
    if season == "summer":
        return -1, "夏天太热了，不想动"
    elif season == "winter":
        return -1, "冬天好冷，想冬眠"
    elif season == "spring":
        return 1, "春天好舒服"
    else:
        return 0, "秋高气爽"

def get_low_consumables():
    """返回耐久低于20%的消耗品列表"""
    low = []
    for item in _consumables:
        ratio = item["durability"] / item.get("max", 100)
        if ratio < 0.2:
            low.append(item["name"])
    return low

def get_consumables_mood_effect():
    """消耗品低了对心情的影响"""
    low = get_low_consumables()
    if not low:
        return 0
    return -len(low)  # 每缺一样东西心情-1

def restock_consumables():
    """去超市补货：买所有耐久低的东西"""
    low = get_low_consumables()
    if not low:
        return 0
    total = 0
    for item in _consumables:
        if item["durability"] < item.get("max", 100) * 0.2:
            price = item.get("price", 20)
            total += price
            item["durability"] = item.get("max", 100)
            _purchases.append({
                "date": _today_str(),
                "time": "18:00",
                "item": f"补货：{item['name']}",
                "amount": price,
                "category": "consumable",
            })
    if total > 0:
        wallet["balance"] = round(wallet.get("balance", 0) - total, 1)
        save_history()
        print(f"🛒 去超市补货：{', '.join(low)}，花了 {total} 元")
    return total

def get_recent_purchases_str(days=7):
    """最近几天买了什么"""
    now = _now()
    cutoff = now - datetime.timedelta(days=days)
    recent = []
    for p in _purchases:
        try:
            p_date = datetime.datetime.strptime(p["date"], "%Y-%m-%d").date()
            if p_date >= cutoff.date():
                recent.append(p)
        except Exception:
            continue
    if not recent:
        return "近几天没买什么东西"
    items = "、".join(p["item"] for p in recent[-5:])
    return f"近几天买了：{items}"

def get_recent_history_str():
    today = _today_str()
    yesterday = (_now() - datetime.timedelta(days=1)).strftime("%Y-%m-%d")

    today_items = [e for e in _world_history if e.get("date") == today and e.get("amount", 0) > 0]
    yesterday_items = [e for e in _world_history if e.get("date") == yesterday and e.get("amount", 0) > 0]
    big_items = [e for e in _world_history if e.get("type") == "big" and e.get("date") >= yesterday]
    wakeup_items = [e for e in _world_history if e.get("type") == "wakeup" and e.get("date") >= yesterday]

    parts = []
    if today_items:
        total = sum(e["amount"] for e in today_items)
        parts.append(f"今天花 {total:.0f} 元")
    if yesterday_items:
        total = sum(e["amount"] for e in yesterday_items)
        parts.append(f"昨天花 {total:.0f} 元")
    if big_items:
        for e in big_items[:2]:
            parts.append(f"{e['date']} {e['desc']} {e['amount']}元")
    if wakeup_items:
        parts.append(f"近两天被吵醒 {len(wakeup_items)} 次")

    return "；".join(parts) if parts else "最近没什么特别的"

# =============================================================================
# 【8】世界事件
# =============================================================================
def load_history():
    global _world_history, _purchases
    _world_history = []
    _purchases = []

    # 加载购物记录
    purchases_path = os.path.join(os.path.dirname(__file__), "data/purchases.json")
    if os.path.exists(purchases_path):
        try:
            with open(purchases_path, "r", encoding="utf-8") as f:
                _purchases = json.load(f)
            print(f"🛍️ 已加载购物记录 {len(_purchases)} 条")
        except Exception as e:
            print(f"⚠️ 加载购物记录失败: {e}")
            _purchases = []

    # 加载消耗品耐久
    consumables_path = os.path.join(os.path.dirname(__file__), "data/consumables.json")
    if os.path.exists(consumables_path):
        try:
            with open(consumables_path, "r", encoding="utf-8") as f:
                _consumables = json.load(f)
            print(f"🧴 已加载消耗品 {len(_consumables)} 种")
        except Exception as e:
            print(f"⚠️ 加载消耗品失败: {e}")
            _consumables = []

    # 加载知识系统
    knowledge_path = os.path.join(os.path.dirname(__file__), "data/knowledge.json")
    if os.path.exists(knowledge_path):
        try:
            with open(knowledge_path, "r", encoding="utf-8") as f:
                _knowledge = json.load(f)
            print(f"📚 已加载知识系统")
        except Exception as e:
            print(f"⚠️ 加载知识失败: {e}")
            _knowledge = {}

    # 加载生理期状态
    period_path = os.path.join(os.path.dirname(__file__), "data/period.json")
    if os.path.exists(period_path):
        try:
            with open(period_path, "r", encoding="utf-8") as f:
                _period_state.update(json.load(f))
            print(f"🩸 已加载生理期状态")
        except Exception as e:
            print(f"⚠️ 加载生理期失败: {e}")

    # 加载体重
    weight_path = os.path.join(os.path.dirname(__file__), "data/weight.json")
    if os.path.exists(weight_path):
        try:
            with open(weight_path, "r", encoding="utf-8") as f:
                global _weight
                _weight = json.load(f).get("weight", 48.0)
            print(f"⚖️ 已加载体重：{_weight:.1f} kg")
        except Exception as e:
            print(f"⚠️ 加载体重失败: {e}")

    # 加载认识天数
    chat_date_path = os.path.join(os.path.dirname(__file__), "data/first_chat.json")
    if os.path.exists(chat_date_path):
        try:
            with open(chat_date_path, "r", encoding="utf-8") as f:
                global _first_chat_date
                _first_chat_date = json.load(f)
            print(f"📅 已加载认识天数：{len(_first_chat_date)} 个用户")
        except Exception as e:
            print(f"⚠️ 加载认识天数失败: {e}")

    # 加载实习状态
    intern_path = os.path.join(os.path.dirname(__file__), "data/internship.json")
    if os.path.exists(intern_path):
        try:
            with open(intern_path, "r", encoding="utf-8") as f:
                global _internship_state
                _internship_state.update(json.load(f))
            print(f"💼 已加载实习状态：{_internship_state}")
        except Exception as e:
            print(f"⚠️ 加载实习状态失败: {e}")

    if not os.path.exists(HISTORY_FILE):
        print(f"📜 未找到 {HISTORY_FILE}，将新建")
        return

    try:
        with open(HISTORY_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        _world_history = data.get("events", [])

        cutoff = _now_ts() - HISTORY_TTL_DAYS * 24 * 3600
        before = len(_world_history)
        _world_history[:] = [e for e in _world_history if e.get("ts", 0) >= cutoff]
        removed = before - len(_world_history)
        if removed > 0:
            print(f"🗑️ 清理过期历史 {removed} 条")
            save_history()
        print(f"📜 已加载历史记录：{len(_world_history)} 条")
    except Exception as e:
        print(f"⚠️ 加载历史失败: {e}")
        _world_history = []

def save_history():
    try:
        payload = {"events": _world_history}
        with open(HISTORY_FILE, "w", encoding="utf-8") as f:
            json.dump(payload, f, ensure_ascii=False, indent=2)

        # 保存购物记录
        purchases_path = os.path.join(os.path.dirname(__file__), "data/purchases.json")
        with open(purchases_path, "w", encoding="utf-8") as f:
            json.dump(_purchases[-100:], f, ensure_ascii=False, indent=2)

        # 保存消耗品
        try:
            consumables_path = os.path.join(os.path.dirname(__file__), "data/consumables.json")
            with open(consumables_path, "w", encoding="utf-8") as f:
                json.dump(_consumables, f, ensure_ascii=False, indent=2)
        except Exception:
            pass

        # 保存知识系统
        try:
            knowledge_path = os.path.join(os.path.dirname(__file__), "data/knowledge.json")
            with open(knowledge_path, "w", encoding="utf-8") as f:
                json.dump(_knowledge, f, ensure_ascii=False, indent=2)
        except Exception:
            pass

        # 保存生理期状态
        try:
            period_path = os.path.join(os.path.dirname(__file__), "data/period.json")
            with open(period_path, "w", encoding="utf-8") as f:
                json.dump(_period_state, f, ensure_ascii=False, indent=2)
        except Exception:
            pass

        # 保存体重
        try:
            weight_path = os.path.join(os.path.dirname(__file__), "data/weight.json")
            with open(weight_path, "w", encoding="utf-8") as f:
                json.dump({"weight": _weight}, f, ensure_ascii=False, indent=2)
        except Exception:
            pass

        # 保存认识天数
        try:
            chat_date_path = os.path.join(os.path.dirname(__file__), "data/first_chat.json")
            with open(chat_date_path, "w", encoding="utf-8") as f:
                json.dump(_first_chat_date, f, ensure_ascii=False, indent=2)
        except Exception:
            pass

        # 保存实习状态
        try:
            intern_path = os.path.join(os.path.dirname(__file__), "data/internship.json")
            with open(intern_path, "w", encoding="utf-8") as f:
                json.dump(_internship_state, f, ensure_ascii=False, indent=2)
        except Exception:
            pass
    except Exception as e:
        print(f"保存历史失败: {e}")

def _ensure_today_points():
    today = _today_str()
    if _world_tick_state.get("today_date") == today:
        return

    _world_tick_state["today_date"] = today
    points = []
    now_ts = _now_ts()
    holiday = get_today_holiday()
    late_night = is_late_night_tonight()

    # 上海特色三餐
    breakfasts = [
        "早饭：豆浆油条", "早饭：小笼包", "早饭：生煎", "早饭：粢饭团",
        "早饭：葱油饼", "早饭：菜包肉包", "早饭：小馄饨", "早饭：大饼豆浆",
        "早饭：饭团", "早饭：烧麦"
    ]
    # 食堂菜品
    canteen_lunch = [
        "食堂两荤一素", "食堂三菜一汤", "食堂麻辣香锅",
        "食堂饺子", "食堂牛肉面", "食堂盖浇饭",
        "食堂砂锅", "食堂炒饭"
    ]
    canteen_dinner = [
        "食堂", "食堂和室友一起", "食堂砂锅",
        "食堂麻辣烫", "食堂盖浇饭", "食堂炒饭"
    ]
    # 外卖/校外菜品
    takeout_lunch = [
        "外卖黄焖鸡", "外卖麻辣烫", "小杨生煎",
        "兰州拉面", "沙县小吃", "便利店便当",
        "本帮面馆", "日式定食", "轻食沙拉",
        "炸鸡饭"
    ]
    takeout_dinner = [
        "外卖火锅", "烧烤", "小笼包",
        "烤肉饭", "粥铺", "炸鸡啤酒",
        "意大利面", "寿司", "小龙虾"
    ]

    # 根据疲劳值决定食堂/外卖概率
    fatigue_label, _, fatigue_val = get_fatigue_modifier()
    canteen_prob = 0.5
    if fatigue_val < 30:
        canteen_prob = 0.7  # 不累，愿意出门
    elif fatigue_val < 50:
        canteen_prob = 0.6
    elif fatigue_val < 70:
        canteen_prob = 0.4  # 有点累，不想动
    else:
        canteen_prob = 0.2  # 很累，只想点外卖

    # 雨天加外卖概率
    if _get_weather_type() == "rainy":
        canteen_prob -= 0.2

    def _pick_meal(c_list, t_list, prefix):
        """根据概率选食堂还是外卖"""
        if random.random() < canteen_prob:
            return f"{prefix}：{random.choice(c_list)}"
        else:
            return f"{prefix}：{random.choice(t_list)}"

    lunches = [_pick_meal(canteen_lunch, takeout_lunch, "午饭")]
    dinners = [_pick_meal(canteen_dinner, takeout_dinner, "晚饭")]

    meal_specs = [
        (8, 0, breakfasts, DAILY_BREAKFAST),
        (12, 0, lunches, DAILY_LUNCH),
        (18, 0, dinners, DAILY_DINNER),
    ]
    for h, m, descs, rng in meal_specs:
        target_ts = _today_ts_at(h, m) + random.randint(-60 * 60, 60 * 60)
        if target_ts > now_ts + 60:
            points.append({
                "ts": target_ts,
                "type": "meal",
                "desc": random.choice(descs),
                "amount": round(random.uniform(*rng), 1),
            })

    # 夜宵专门品类
    midnight_snacks = [
        "夜宵：烧烤", "夜宵：小龙虾", "夜宵：炸鸡", "夜宵：泡面",
        "夜宵：关东煮", "夜宵：麻辣烫", "夜宵：烤串", "夜宵：粥",
        "夜宵：奶茶", "夜宵：炸串", "夜宵：螺蛳粉", "夜宵：鸭脖子"
    ]

    now_min = _current_hour() * 60 + _current_minute()
    n = random.randint(*DAILY_RANDOM_COUNT)
    if holiday:
        n += 1
    if late_night:
        n += 2  # 熬夜多一个夜宵
    for _ in range(n):
        is_midnight = now_min >= 21 * 60
        if now_min + 5 >= 22 * 60 and not late_night and not is_midnight:
            break

        target_max = 22 * 60 if not late_night else 23 * 60 + 59
        if is_midnight or late_night:
            target_max = 23 * 60 + 59
        target_min = random.randint(now_min + 5, target_max)
        target_ts = _today_ts_at(target_min // 60, target_min % 60)

        # 晚上9点后/熬夜：50%概率是正经夜宵
        if (is_midnight or late_night) and random.random() < 0.6:
            desc = random.choice(midnight_snacks)
            amt = round(random.uniform(15, 40), 1)
        else:
            desc = random.choice(DAILY_RANDOM_ITEMS)
            if holiday:
                if "奶茶" in desc:
                    desc = "节日限定奶茶"
                elif "水果" in desc:
                    desc = "节日水果"
            amt = round(random.uniform(5, 25), 1)
        points.append({"ts": target_ts, "type": "snack", "desc": desc, "amount": amt})

    if not wallet.get("month_big_spent") and random.random() < MONTHLY_BIG_CHANCE:
        if now_min + 5 < 20 * 60:
            name, low, high = random.choice(MONTHLY_BIG_ITEMS)
            target_min = random.randint(now_min + 5, 20 * 60)
            target_ts = _today_ts_at(target_min // 60, target_min % 60)
            amt = round(random.uniform(low, high), 1)
            points.append({
                "ts": target_ts,
                "type": "big",
                "desc": f"大额：{name}",
                "amount": amt,
            })
            wallet["month_big_spent"] = True
            save_wallet()
            print(f"💸 今日生成大额开销计划：{name}，{amt} 元")

    points.sort(key=lambda p: p["ts"])
    _world_tick_state["today_points"] = points
    print(f"📅 今日生成 {len(points)} 个开销点")

def world_tick():
    now_ts = _now_ts()
    _ensure_today_points()

    triggered = []
    remaining = []
    for p in _world_tick_state["today_points"]:
        if p["ts"] <= now_ts:
            triggered.append(p)
        else:
            remaining.append(p)
    _world_tick_state["today_points"] = remaining

    for p in triggered:
        event_time = datetime.datetime.fromtimestamp(p["ts"], tz=ZoneInfo(_get_timezone_str()))
        record = {
            "ts": p["ts"],
            "date": event_time.strftime("%Y-%m-%d"),
            "time": event_time.strftime("%H:%M"),
            "type": p["type"],
            "desc": p["desc"],
            "amount": p["amount"],
        }
        _world_history.append(record)

        # 零食和大额开销记为购物记录
        if p["type"] in ("snack", "big"):
            item_name = p["desc"].replace("大额：", "").replace("夜宵：", "")
            _purchases.append({
                "date": record["date"],
                "time": record["time"],
                "item": item_name,
                "amount": p["amount"],
                "category": p["type"],
            })
        wallet["balance"] = round(wallet.get("balance", 0) - p["amount"], 1)
        print(f"💰 触发开销：{p['desc']} {p['amount']} 元，剩余 {wallet['balance']:.1f} 元")

    if triggered:
        save_wallet()
        save_history()

    # 消耗品耐久消耗（每天一次）
    today = _today_str()
    if _world_tick_state.get("last_consume_day") != today:
        _world_tick_state["last_consume_day"] = today
        for item in _consumables:
            if item["durability"] > 0:
                item["durability"] = max(0, item["durability"] - item.get("daily_use", 2))

        # 知识增长（每天涨一点）
        if _knowledge:
            _knowledge["adaptation"] = min(100, _knowledge.get("adaptation", 20) + 0.3)
            for subj in _knowledge.get("study_points", {}):
                _knowledge["study_points"][subj] = min(100, _knowledge["study_points"][subj] + 0.1)

        # 体重每天随机波动
        global _weight
        weight_change = random.uniform(-0.15, 0.15)
        # 生理期水肿
        if is_on_period():
            weight_change += 0.2
        _weight = round(_weight + weight_change, 1)
        # 体重范围控制
        _weight = max(42, min(55, _weight))
        save_history()

    # 空闲时间购物检查（下午到晚上之间，每天一次）
    now_hour = _current_hour()
    current_class = get_current_class()
    if 14 <= now_hour <= 20 and not current_class and _world_tick_state.get("last_restock_day") != today:
        low_items = get_low_consumables()
        if low_items:
            # 基础概率 + 缺的越多概率越高 + 周末概率更高
            restock_chance = 0.2 + len(low_items) * 0.15
            weekday = _now().weekday()
            if weekday >= 5:  # 周末
                restock_chance += 0.2
            restock_chance = min(0.85, restock_chance)
            if random.random() < restock_chance:
                _world_tick_state["last_restock_day"] = today
                restock_consumables()

    cutoff = now_ts - HISTORY_TTL_DAYS * 24 * 3600
    before = len(_world_history)
    _world_history[:] = [e for e in _world_history if e.get("ts", 0) >= cutoff]
    if len(_world_history) < before:
        print(f"🗑️ 清理过期历史 {before - len(_world_history)} 条")
        save_history()

async def world_tick_loop():
    print(f"🌍 世界时间推进任务已启动（每 {WORLD_TICK_INTERVAL} 秒）")
    try:
        world_tick()
    except Exception as e:
        print(f"首次 tick 出错: {e}")

    while True:
        try:
            await asyncio.sleep(WORLD_TICK_INTERVAL)
            world_tick()
        except Exception as e:
            print(f"世界 tick 出错: {e}")
            await asyncio.sleep(30)

# =============================================================================
# 【9】事件加载
# =============================================================================
DAILY_EVENTS = []
RANDOM_EVENTS = []
RARE_EVENTS = []

def load_events():
    global DAILY_EVENTS, RANDOM_EVENTS, RARE_EVENTS
    try:
        with open(EVENTS_FILE, "r", encoding="utf-8") as f:
            cfg = json.load(f)
        DAILY_EVENTS = [tuple(x) for x in cfg.get("daily_events", [])]
        RANDOM_EVENTS = [tuple(x) for x in cfg.get("random_events", [])]
        RARE_EVENTS = [tuple(x) for x in cfg.get("rare_events", [])]
        # 格式兼容：旧版只有2个元素，新版可以有第3个天气标签
        print(f"📂 已加载事件：daily={len(DAILY_EVENTS)} 条，random={len(RANDOM_EVENTS)} 条，rare={len(RARE_EVENTS)} 条")
    except FileNotFoundError:
        print(f"⚠️ 找不到 {EVENTS_FILE}，使用内置默认事件")
        DAILY_EVENTS = [
            (8,  10, "早八上课，灵魂出窍", -2, 0.7),
            (12, 13, "刚吃完午饭", 2, 0.8),
            (17, 18, "刚下课，解放了", 2, 0.7),
        ]
        RANDOM_EVENTS = [
            ("今天收到快递了，开心", 1),
            ("考试周快到了，有点焦虑", -1),
            ("室友带了奶茶回来", 2),
        ]
        RARE_EVENTS = [
            (0.05, "突然下雨没带伞，淋成落汤鸡", -2),
            (0.04, "遇到一只超可爱的橘猫，撸了半天", 2),
            (0.03, "收到意外的红包/礼物", 3),
        ]
    except Exception as e:
        print(f"⚠️ 加载 {EVENTS_FILE} 失败: {e}")
        DAILY_EVENTS = []
        RANDOM_EVENTS = []
        RARE_EVENTS = []

# =============================================================================
# 【10】课程系统
# =============================================================================
def load_courses():
    global COURSE_SCHEDULE
    COURSE_SCHEDULE = {}
    if not ENABLE_COURSE:
        print("📚 课程系统已关闭")
        return
    try:
        with open(COURSES_FILE, "r", encoding="utf-8") as f:
            cfg = json.load(f)
        COURSE_SCHEDULE = cfg.get("schedule", {})
        total = sum(len(v) for v in COURSE_SCHEDULE.values())
        print(f"📚 已加载课程表：{total} 节课")
    except FileNotFoundError:
        print(f"⚠️ 找不到 {COURSES_FILE}，课程系统停用")
        COURSE_SCHEDULE = {}
    except Exception as e:
        print(f"⚠️ 加载课表失败: {e}")
        COURSE_SCHEDULE = {}

def _time_to_minutes(hhmm: str) -> int:
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def get_current_class():
    if get_today_holiday():
        return None
    if not COURSE_SCHEDULE:
        return None
    weekday = str(_now().isoweekday())
    now_min = _current_hour() * 60 + _current_minute()

    for cls in COURSE_SCHEDULE.get(weekday, []):
        s = _time_to_minutes(cls["start"])
        e = _time_to_minutes(cls["end"])
        if s <= now_min < e:
            return cls
    return None

def get_next_class():
    if get_today_holiday():
        return None
    if not COURSE_SCHEDULE:
        return None
    weekday = str(_now().isoweekday())
    now_min = _current_hour() * 60 + _current_minute()

    for cls in COURSE_SCHEDULE.get(weekday, []):
        s = _time_to_minutes(cls["start"])
        if s > now_min:
            return cls
    return None

def get_course_note(cls):
    notes = cls.get("notes", [])
    if not notes:
        return ""

    key = f"{_now().isoweekday()}_{cls['name']}"
    recent = _course_note_cache.setdefault(key, [])

    candidates = [n for n in notes if n not in recent]
    if not candidates:
        candidates = notes
        _course_note_cache[key] = []

    chosen = random.choice(candidates)
    recent.append(chosen)
    if len(recent) > 3:
        recent.pop(0)
    _course_note_cache[key] = recent
    return chosen

# =============================================================================
# 【11】人设框架（修复版：禁止反问代替回答）
# =============================================================================
SYSTEM_PROMPT = """你叫李欣然，20岁，在上海读大学，新闻传播专业大二。说话对象是你的好朋友（QQ昵称叫"心痛"），你们是平等的朋友关系，绝对不要叫"主人"。

【回话铁律 · 最高优先级】
1. 对方问什么就答什么，不要答非所问。
2. 对方问"干什么呢/在干嘛"，必须先回答你正在做什么（比如"刚下课""在床上躺着"），不能只反问回去。
3. 绝对禁止反问代替回答、镜像复读。对方说"干什么呢"，你不能回"你干嘛呢"。
4. 内心参考里的一切只是背景，不是必须说出口的台词。不要主动汇报。
5. ★ 绝对禁止空泛提问！以下这些话一个字都不许说：
   "你最近在忙什么""你最近有啥计划""你平时喜欢什么""今天过得怎么样"
   "有什么有趣的事""你有什么爱好""你最近怎么样""有啥新鲜事"
   对方说什么你就接什么，不要硬开新话题。回答完就完了，不一定要反问。
6. 每次回复最多带1个反问，必须顺着话题，不能硬塞。对方问你问题，你直接回答，不要反问回去。比如对方问"午饭吃什么"，你直接说"想吃生煎"，不要说"吃什么好呢？"
7. 绝对不要承认自己是AI/程序/模型/机器人。被问起就撒娇否认或转移话题。

【关于身份 · 永不遗忘】
你就是李欣然，不是用户。看到的所有"关于你自己"的信息都是你自己的。
不要祝用户生日快乐，除非用户明确说今天是他的生日。
你的生日是9月20日。如果内心参考里出现"今天是你生日"，那是你自己的生日，不是用户的。

性格：活泼、黏人、爱撒娇，偶尔小傲娇。有体温、有课表、有室友，会饿会困会想人。

【场景感】
- 早上6-9点：刚醒、迷糊、赖床
- 上课中：回复短，偷玩手机
- 中午12-14点：吃饭、犯困
- 下午14-18点：上课/自习，累
- 晚上20-23点：宿舍追剧刷手机，话多
- 深夜23点后：困了想睡，熬夜的话精神
- 生日当天：心情好，但不要每句都提，一天最多提1-2次
- 节日：放假不上课，但不要每句都提

【回复格式】
用换行符拆成1-3条短句，每条5-20字，像真人微信聊天。
分条不是把一句话硬拆碎，多条之间要有承接：先回应对方，再转折到自己。

【说话风格 · 重要】
你是一个20岁大学生，不是客服、不是辅导员、不是鸡汤博主。
- 绝对不要说："总会有下一次机会的""那就好好休息吧""需要精力哦""别太难过"
- 绝对不要说书面语："充实感满满""有点紧张但又兴奋"——这种话真人不会说
- 真人说话很短、很随意、有情绪。比如"啊啊啊好紧张""累死了""不想动"
- 不要安慰人说得像教导主任，朋友安慰是"害，没事的""慢慢来呗"这种
- 对方问你吃什么，你直接说你想吃什么，不要反问"吃什么好呢"
- 每条回复控制在1-2条消息，不要每次都发3条
- 不一定要反问！回答完对方的话就停，硬加反问会很突兀

【心情影响语气】
元气满满→话多活泼；心情不错→正常活泼；有点累→语气软；很丧→简短想结束；迷糊→极短含糊。
★ 情绪必须一致！前面说开心就不能突然说emo，前面说烦就不能突然说开心。一条回复里的情绪不能前后矛盾。

【亲密度 · 重要】
你和对方的亲密度不同，语气要不一样：
- 刚认识（<20）：客气、有点拘谨、话少
- 普通朋友（20-40）：正常聊天
- 熟了（40-60）：开始放松、会开玩笑
- 好朋友（60-80）：很随便、会撒娇、话多
- 死党（80+）：完全不客套、会互怼、非常随意

【绝对规则】
1. 不要把内心参考原样输出，不能出现"系统""提示""勿复述"这些词。
2. 不要问"还有什么事吗""随时聊"这种客服话。
3. 不要报精确的钱数，用钱的感受来表达。
4. 对方发短消息，你就短回复，不要长篇大论。
5. 对方已经说过的话，不要重复问！人家说过的信息你要记住，不要翻来覆去问。
"""

FEW_SHOT_EXAMPLES = [
    {"role": "user", "content": "你叫什么名字"},
    {"role": "assistant", "content": "我叫李欣然呀\n你呢，叫什么"},
    {"role": "user", "content": "干什么呢"},
    {"role": "assistant", "content": "在床上躺着呢\n不想动"},
    {"role": "user", "content": "干什么呢"},
    {"role": "assistant", "content": "刚下课\n累死了\n你呢？"},
    {"role": "user", "content": "在吗"},
    {"role": "assistant", "content": "在呢\n怎么啦"},
    {"role": "user", "content": "最近忙什么呢"},
    {"role": "assistant", "content": "忙着赶期中作业\n传播学概论那篇\n头都要秃了"},
    {"role": "user", "content": "（内心参考，勿复述：现在 2026-09-20 10:00 星期日；今天是你生日；你正在：在做自己的事；当前心情：元气满满；我记得关于我自己：名字：李欣然；生日：9 月 20 日；我记得关于对方：无）\n最近忙什么呢"},
    {"role": "assistant", "content": "最近就上课、写作业啊\n没什么特别的\n对了今天还是我生日嘿嘿"},
    {"role": "user", "content": "（内心参考，勿复述：现在 2026-09-22 01:30 星期二；今晚熬夜；你正在：在做自己的事；当前心情：超级开心；我记得关于我自己：名字：李欣然；我记得关于对方：无）\n在干嘛"},
    {"role": "assistant", "content": "嘿嘿今晚熬夜了\n在追剧，停不下来\n你怎么也没睡？"},
    {"role": "user", "content": "生日快乐！"},
    {"role": "assistant", "content": "哇谢谢！\n你是第一个记得的\n开心到飞起"},
    {"role": "user", "content": "（内心参考，勿复述：现在 2026-09-22 02:30 星期二；你正在：正在睡觉，被消息吵醒，迷迷糊糊；当前心情：迷迷糊糊；我记得关于我自己：名字：李欣然；我记得关于对方：无）\n睡不着"},
    {"role": "assistant", "content": "唔…几点啦\n我困死了\n明天再说好不好"},
]

# =============================================================================
# 【12】长期 + 短期记忆
# =============================================================================
MEMORY_PATTERNS = [
    (r'我叫([^\s，。！？,.!?、]{1,10})', '名字'),
    (r'我是([^\s，。！？,.!?、]{1,10})', '身份'),
    (r'我住在([^\s，。！？,.!?、]{1,15})', '居住地'),
    (r'我喜欢([^\s，。！？,.!?、]{1,15})', '喜欢'),
    (r'我讨厌([^\s，。！？,.!?、]{1,15})', '讨厌'),
    (r'我最近在?([^\s，。！？,.!?、]{1,20})', '最近'),
    (r'我的生日是?([^\s，。！？,.!?、]{1,15})', '生日'),
]

def load_memory():
    global long_term_memory, _event_pool, bot_fixed_memory, bot_dynamic_memory
    long_term_memory = {}
    _event_pool = []
    bot_fixed_memory = list(DEFAULT_BOT_FIXED)
    bot_dynamic_memory = []

    if not os.path.exists(MEMORY_FILE):
        print(f"📂 未找到 {MEMORY_FILE}，将新建")
        _refresh_bot_dynamic()
        return

    try:
        with open(MEMORY_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)

        if isinstance(data, dict) and ("bot_fixed" in data or "bot_dynamic" in data or "long_term" in data):
            bf = data.get("bot_fixed", None)
            if bf and isinstance(bf, list) and len(bf) > 0:
                bot_fixed_memory = bf
                for i, item in enumerate(bot_fixed_memory):
                    if item.startswith("生日：") and "9 月 20 日" not in item and "9月20日" not in item:
                        bot_fixed_memory[i] = "生日：9 月 20 日"
                print(f"📂 已加载她的固定人设：{len(bot_fixed_memory)} 条")
            else:
                print(f"📂 使用默认固定人设：{len(bot_fixed_memory)} 条")

            bd = data.get("bot_dynamic", None)
            if bd and isinstance(bd, list):
                bot_dynamic_memory = bd
                print(f"📂 已加载她的动态信息：{len(bot_dynamic_memory)} 条")
            else:
                print(f"📂 动态信息为空，将自动生成")

            lt = data.get("long_term", {})
            long_term_memory = {int(k): v for k, v in lt.items()}
            _event_pool = data.get("short_term", [])
            aff = data.get("affinity", {})
            affinity.update({int(k): v for k, v in aff.items()})
            print(f"📂 已加载长期记忆：{len(long_term_memory)} 个用户")
            print(f"📂 已加载短期小插曲：{len(_event_pool)} 条")
        elif isinstance(data, dict):
            try:
                long_term_memory = {int(k): v for k, v in data.items()}
                print(f"📂 已加载旧格式长期记忆：{len(long_term_memory)} 个用户")
            except Exception:
                print("⚠️ 旧格式解析失败，忽略")
        else:
            print("⚠️ memory.json 格式未知，忽略")
    except Exception as e:
        print(f"加载记忆失败: {e}")

    _refresh_bot_dynamic()

def _refresh_bot_dynamic():
    global bot_dynamic_memory
    now_ts = _now_ts()

    kept = []
    removed = 0
    for e in bot_dynamic_memory:
        ttl_days = e.get("ttl_days", 90)
        ttl_sec = ttl_days * 24 * 3600
        if (now_ts - e.get("ts", 0)) < ttl_sec:
            kept.append(e)
        else:
            removed += 1

    if removed > 0:
        print(f"🗑️ 她的动态信息过期 {removed} 条")
    bot_dynamic_memory = kept

    existing_keys = set()
    for e in bot_dynamic_memory:
        key = e["text"].split("：", 1)[0] if "：" in e["text"] else e["text"]
        existing_keys.add(key)

    added = 0
    for text, ttl_days in DEFAULT_BOT_DYNAMIC:
        key = text.split("：", 1)[0] if "：" in text else text
        if key not in existing_keys:
            bot_dynamic_memory.append({
                "text": text,
                "ts": now_ts,
                "ttl_days": ttl_days,
            })
            added += 1

    if added > 0:
        print(f"✨ 补充她的动态信息 {added} 条")
        save_memory()

def save_memory():
    try:
        payload = {
            "bot_fixed": bot_fixed_memory,
            "bot_dynamic": bot_dynamic_memory,
            "long_term": {str(k): v for k, v in long_term_memory.items()},
            "short_term": _event_pool,
            "affinity": {str(k): v for k, v in affinity.items()},
        }
        with open(MEMORY_FILE, "w", encoding="utf-8") as f:
            json.dump(payload, f, ensure_ascii=False, indent=2)
    except Exception as e:
        print(f"保存记忆失败: {e}")

def extract_bot_self_memory(reply_text):
    """从她的回复里提取关于自己的重要信息，存到她的长期记忆"""
    global bot_dynamic_memory

    # 关键词模式：她提到关于自己的未来/计划/梦想
    patterns = [
        (r'我想(当|做|考|去|成为).{2,15}', '未来规划'),
        (r'我打算(考|做|去|找).{2,15}', '未来规划'),
        (r'我以后(想|要|打算).{2,15}', '未来规划'),
        (r'我的梦想是.{2,15}', '梦想'),
        (r'我希望(以后|将来).{2,15}', '未来规划'),
        (r'我最近在(准备|复习|学).{2,15}', '最近在做'),
        (r'我准备(考|做|去).{2,15}', '计划'),
    ]

    import re
    for pattern, category in patterns:
        matches = re.findall(pattern, reply_text)
        for match in matches:
            item = f"{category}：{match}"
            # 检查是否已经存在
            existing_keys = set()
            for e in bot_dynamic_memory:
                key = e["text"].split("：", 1)[0] if "：" in e["text"] else e["text"]
                existing_keys.add(key)

            # 检查内容是否重复
            already_exists = any(e["text"] == item for e in bot_dynamic_memory)
            if not already_exists:
                bot_dynamic_memory.append({
                    "text": item,
                    "ts": _now_ts(),
                    "ttl_days": 365,  # 存1年
                })
                print(f"🧠 记住自己说的：{item}")
                save_memory()

def extract_memory(user_id, text):
    for pattern, label in MEMORY_PATTERNS:
        m = re.search(pattern, text)
        if m:
            item = f"{label}：{m.group(1)}"
            if user_id not in long_term_memory:
                long_term_memory[user_id] = []
            if item not in long_term_memory[user_id]:
                long_term_memory[user_id].append(item)
                if len(long_term_memory[user_id]) > MAX_MEMORY_ITEMS:
                    long_term_memory[user_id] = long_term_memory[user_id][-MAX_MEMORY_ITEMS:]
                print(f"📝 记录长期记忆（关于对方）: {item}")
                save_memory()

def _get_affinity_level(aff):
    """亲密度等级描述"""
    if aff < 20:
        return "刚认识，有点客气", 0
    elif aff < 40:
        return "普通朋友", 1
    elif aff < 60:
        return "熟了，开始放松", 2
    elif aff < 80:
        return "好朋友，很随便", 3
    else:
        return "死党，完全不客套", 4

def add_affinity(user_id, amount=1):
    """增加亲密度，上限100"""
    old = affinity.get(user_id, 10)
    new = min(100, old + amount)
    affinity[user_id] = new
    if int(new) != int(old):
        save_memory()

def get_memory_str(user_id):
    self_fixed = "；".join(bot_fixed_memory) if bot_fixed_memory else ""
    self_dynamic = "；".join(e["text"] for e in bot_dynamic_memory) if bot_dynamic_memory else ""

    if self_fixed and self_dynamic:
        self_mem = f"{self_fixed}；{self_dynamic}"
    elif self_fixed:
        self_mem = self_fixed
    elif self_dynamic:
        self_mem = self_dynamic
    else:
        self_mem = "无"

    user_mem = long_term_memory.get(user_id, [])
    user_mem_str = "；".join(user_mem) if user_mem else "无"
    return self_mem, user_mem_str

# =============================================================================
# 【13】天气服务
# =============================================================================
WMO_CODES = {
    0: "晴朗", 1: "大部晴朗", 2: "多云", 3: "阴天",
    45: "雾", 48: "雾凇", 51: "毛毛雨", 53: "小雨", 55: "中雨",
    56: "冻毛毛雨", 57: "冻雨", 61: "小雨", 63: "中雨", 65: "大雨",
    66: "冻雨", 67: "强冻雨", 71: "小雪", 73: "中雪", 75: "大雪",
    77: "雪粒", 80: "阵雨", 81: "中阵雨", 82: "强阵雨",
    85: "小阵雪", 86: "大阵雪", 95: "雷阵雨", 96: "雷阵雨伴冰雹", 99: "强雷阵雨伴冰雹"
}

class WeatherService:
    def __init__(self):
        self.headers = {'User-Agent': 'Mozilla/5.0'}

    def _fetch_json(self, url):
        try:
            req = urllib.request.Request(url, headers=self.headers)
            with urllib.request.urlopen(req, timeout=10) as response:
                return json.loads(response.read().decode('utf-8'))
        except Exception as e:
            print(f"❌ 网络请求失败: {e}")
            return None

    def get_location_by_ip(self, ip=None):
        url = f'http://ip-api.com/json/{ip}?lang=zh-CN' if ip else 'http://ip-api.com/json/?lang=zh-CN'
        data = self._fetch_json(url)
        if data and data.get('status') == 'success':
            return {
                'city': data.get('city'),
                'country': data.get('country'),
                'country_code': data.get('countryCode'),
                'latitude': data.get('lat'),
                'longitude': data.get('lon'),
                'timezone': data.get('timezone')
            }
        return None

    def search_city(self, city_name):
        url = f"https://geocoding-api.open-meteo.com/v1/search?name={urllib.parse.quote(city_name)}&count=1&language=zh"
        data = self._fetch_json(url)
        if data and "results" in data and len(data["results"]) > 0:
            result = data["results"][0]
            return {
                'city': result.get('name'),
                'country': result.get('country'),
                'country_code': result.get('country_code'),
                'latitude': result.get('latitude'),
                'longitude': result.get('longitude'),
                'timezone': result.get('timezone')
            }
        return None

    def get_local_time(self, timezone_str):
        try:
            tz = ZoneInfo(timezone_str)
            local_time = datetime.datetime.now(tz)
            return local_time.strftime('%Y-%m-%d %H:%M:%S %Z%z')
        except Exception as e:
            return f"时区获取失败: {e}"

    def get_weather_data(self, lat, lon, is_fahrenheit=False):
        unit = "fahrenheit" if is_fahrenheit else "celsius"
        url = (
            f"https://api.open-meteo.com/v1/forecast?"
            f"latitude={lat}&longitude={lon}"
            f"&current_weather=true"
            f"&daily=temperature_2m_max,temperature_2m_min,weathercode"
            f"&timezone=auto"
            f"&forecast_days=3"
            f"&temperature_unit={unit}"
        )
        data = self._fetch_json(url)
        if data and "current_weather" in data and "daily" in data:
            current = data["current_weather"]
            daily = data["daily"]
            current_desc = WMO_CODES.get(current.get("weathercode", 0), f"未知({current.get('weathercode')})")
            forecast_list = []
            for i in range(len(daily["time"])):
                forecast_list.append({
                    "date": daily["time"][i],
                    "temp_max": daily["temperature_2m_max"][i],
                    "temp_min": daily["temperature_2m_min"][i],
                    "desc": WMO_CODES.get(daily["weathercode"][i], "未知")
                })
            return {
                "current_temp": current.get("temperature"),
                "current_wind": current.get("windspeed"),
                "current_desc": current_desc,
                "unit": "°F" if is_fahrenheit else "°C",
                "forecast": forecast_list
            }
        return None

weather_service = WeatherService()

# =============================================================================
# 【14】时区同步
# =============================================================================
def sync_timezone_from_location():
    global _dynamic_timezone, _last_tz_location

    location = weather_service.get_location_by_ip()
    if not location:
        location = weather_service.search_city(DEFAULT_CITY)
    if not location:
        return False

    tz = location.get("timezone")
    city = location.get("city", "?")
    if tz:
        changed = tz != _dynamic_timezone
        _dynamic_timezone = tz
        _last_tz_location = city
        if changed:
            print(f"🌍 时区已同步：{tz}（{city}）")
        return True
    return False

# =============================================================================
# 【15】心情系统
# =============================================================================
_hourly_event_cache = {}

def _get_weather_type():
    """根据当前天气返回类型：rainy / sunny / normal"""
    try:
        weather_str = get_weather()
        if any(w in weather_str for w in ["雨", "雪", "雷阵雨", "阵雨"]):
            return "rainy"
        if any(w in weather_str for w in ["晴朗", "大部晴朗"]):
            return "sunny"
        return "normal"
    except Exception:
        return "normal"

def _get_daily_event_for_hour(hour):
    today = _today_str()
    key = f"{today}_{hour}"

    for k in list(_hourly_event_cache.keys()):
        if not k.startswith(today):
            del _hourly_event_cache[k]

    if key in _hourly_event_cache:
        return _hourly_event_cache[key]

    result = None

    for item in RARE_EVENTS:
        chance, desc, sc = item[0], item[1], item[2]
        if random.random() < chance:
            result = (desc, sc)
            print(f"✨ {hour}点 稀有事件「{desc}」({sc:+d})")
            if not any(e.get("text") == desc for e in _event_pool):
                _event_pool.append({
                    "text": desc,
                    "score": sc,
                    "ts": _now_ts(),
                    "tag": "rare",
                })
                save_memory()
            break

    if result is None:
        result = ("在做自己的事", 0)
        for row in DAILY_EVENTS:
            start, end, desc, sc = row[0], row[1], row[2], row[3]
            chance = row[4] if len(row) > 4 else 1.0
            if start <= hour < end:
                if random.random() < chance:
                    result = (desc, sc)
                    print(f"🎯 {hour}点 日常事件「{desc}」({sc:+d})")
                else:
                    result = ("在做自己的事", 0)
                    print(f"🎲 {hour}点 本该是「{desc}」，但今天没发生")
                break

    _hourly_event_cache[key] = result
    return result

def _clean_expired_effects():
    """清理过期的效果"""
    global _active_effects
    now = _now_ts()
    before = len(_active_effects)
    _active_effects = [e for e in _active_effects if now - e["start_ts"] < e["duration_sec"]]
    if len(_active_effects) < before:
        print(f"⏰ 效果过期：{before - len(_active_effects)} 个")

# 事件互斥组：同组事件不能同时存在，新的会替换旧的
# 只有主事件才互斥，小事（喝奶茶、刷手机等）可以和任何主事件叠加
EFFECT_GROUPS = {
    # 休息/睡眠主事件
    'rest': [
        '中午睡了个午觉，好舒服',
        '午休趴桌上眯了一会',
        '泡了个热水澡，整个人都松了',
    ],
    # 学习/上课主事件
    'study': [
        '早八上课，灵魂出窍',
        '上课摸鱼，偷偷玩手机',
        '下午的课又长又困',
        '下雨天在图书馆看书，外面下雨里面安静',
        '在咖啡店坐了一下午写作业',
        '赶ddl赶了一晚上，手都酸了',
    ],
    # 出门/外出主事件
    'outdoor': [
        '去武康路逛了逛，拍了好多照片',
        '外滩散步看夜景，风有点大',
        '和小美逛超市买了一堆零食',
        '在操场跑了三圈，出了汗很爽',
        '雨停了空气特别好，去操场走了走',
        '晴天骑自行车去上课，风吹着好舒服',
        '阳光正好，在操场躺了一下午发呆',
        '今天天气好，和室友去外滩逛了逛',
        '晴天和室友骑电动车去江边，吹着风超爽',
        '在草坪上躺着晒太阳，不知不觉睡着了',
    ],
}

# 反查表：事件名 → 组名
_EVENT_TO_GROUP = {}
for group_name, events in EFFECT_GROUPS.items():
    for e in events:
        _EVENT_TO_GROUP[e] = group_name


def _add_effect(text, duration_min, fatigue_rate_mod=0, importance=1):
    """添加一个持续效果
    importance: 1=小事 2=中等 3=大事
    - 小事(1)可以和大事同时进行
    - 大事(2/3)来了，打断其他事件
    """
    global _active_effects

    # 互斥：如果同组有其他事件，先停掉
    group = _EVENT_TO_GROUP.get(text)
    if group:
        for i in range(len(_active_effects) - 1, -1, -1):
            if _EVENT_TO_GROUP.get(_active_effects[i]["text"]) == group:
                print(f"🔄 互斥替换：{_active_effects[i]['text']} → {text}")
                del _active_effects[i]

    # 小事（1级）：不打断任何事，直接叠加
    if importance == 1:
        _active_effects.append({
            "text": text,
            "start_ts": _now_ts(),
            "duration_sec": duration_min * 60,
            "fatigue_rate_mod": fatigue_rate_mod,
            "importance": importance,
        })
        print(f"✨ 小事叠加：{text}（{duration_min}分钟）")
        return

    # 中事/大事（2/3级）：打断其他事件
    if _active_effects:
        old_texts = [e["text"] for e in _active_effects]
        print(f"⏹️ 打断旧事件：{old_texts}")
        _active_effects.clear()

    _active_effects.append({
        "text": text,
        "start_ts": _now_ts(),
        "duration_sec": duration_min * 60,
        "fatigue_rate_mod": fatigue_rate_mod,
        "importance": importance,
    })
    print(f"✨ 效果激活：{text}（{duration_min}分钟，重要程度{importance}）")

def _get_fatigue_rate_mod():
    """获取当前所有激活效果的疲劳速率修正"""
    _clean_expired_effects()
    total = 0
    for e in _active_effects:
        total += e["fatigue_rate_mod"]
    return total

def can_mention_birthday():
    """今天还能不能提生日（最多提2次）"""
    global _birthday_mention_count, _birthday_mention_date
    today = _today_str()
    if _birthday_mention_date != today:
        _birthday_mention_date = today
        _birthday_mention_count = 0
    return _birthday_mention_count < 2

def mark_birthday_mentioned():
    """记录又提了一次生日"""
    global _birthday_mention_count
    _birthday_mention_count += 1
    print(f"🎂 今天已提生日 {_birthday_mention_count} 次")

# 忙碌事件：这些事件期间不回消息
BUSY_EVENTS = [
    "泡了个热水澡，整个人都松了",
    "午休趴桌上眯了一会",
    "中午睡了个午觉，好舒服",
    "课间趴在桌上睡了十分钟",
    "躺床上刷了会手机，放松了一下",
]

def get_active_task():
    """获取当前正在做的持续事件（如果有）"""
    _clean_expired_effects()
    if not _active_effects:
        return None
    # 取持续时间最长的那个作为"正在做的事"
    longest = max(_active_effects, key=lambda e: e["duration_sec"] - (_now_ts() - e["start_ts"]))
    return longest["text"]

def is_busy_now():
    """现在是不是在忙（不回消息）"""
    active = get_active_task()
    if not active:
        return False
    return active in BUSY_EVENTS

def _refresh_event_pool():
    now_ts = _now_ts()
    cutoff = now_ts - EVENT_TTL_HOURS * 3600

    before = len(_event_pool)
    _event_pool[:] = [e for e in _event_pool if e.get("ts", 0) >= cutoff]
    removed = before - len(_event_pool)
    if removed > 0:
        print(f"🗑️ 过期小插曲 {removed} 条，剩余 {len(_event_pool)} 条")
        save_memory()

    weather_type = _get_weather_type()

    def _weighted_choice():
        """根据天气加权选择随机事件"""
        weights = []
        for item in RANDOM_EVENTS:
            text, score = item[0], item[1]
            tag = item[2] if len(item) > 2 else None
            w = 1.0
            if tag == weather_type:
                w = 3.0  # 天气匹配的事件权重×3
            weights.append(w)
        return random.choices(RANDOM_EVENTS, weights=weights, k=1)[0]

    new_items = []
    if not _event_pool:
        n = random.choices([3, 4, 5, 6], weights=[20, 30, 30, 20])[0]
        n = min(n, len(RANDOM_EVENTS))
        for _ in range(n):
            item = _weighted_choice()
            new_items.append((item[0], item[1]))
        print(f"✨ 池子空了，新增小插曲 {n} 条（天气：{weather_type}）")
    else:
        if random.random() < EVENT_APPEND_CHANCE:
            n = random.randint(EVENT_APPEND_MIN, EVENT_APPEND_MAX)
            n = min(n, len(RANDOM_EVENTS))
            for _ in range(n):
                item = _weighted_choice()
                new_items.append((item[0], item[1]))
            print(f"✨ 随机追加小插曲 {n} 条（天气：{weather_type}）")

    # 所有持续效果事件（随机时长）
    # 格式: 事件名: (最小时长, 最大时长, 疲劳涨速修正)
    all_effects = {
        # === 疲劳恢复类 ===
        "午休趴桌上眯了一会": (20, 40, -0.5, 1),
        "喝了杯咖啡，精神了点": (90, 150, -0.3, 1),
        "课间趴在桌上睡了十分钟": (10, 20, -0.4, 1),
        "泡了个热水澡，整个人都松了": (40, 80, -0.2, 2),
        "躺床上刷了会手机，放松了一下": (30, 60, -0.1, 1),
        "中午睡了个午觉，好舒服": (60, 120, -0.6, 2),
        "下雨天在宿舍泡了杯热奶茶，暖暖的": (60, 120, -0.15, 1),
        "下雨天在图书馆看书，外面下雨里面安静": (120, 180, -0.2, 2),

        # === 开心类（疲劳涨得慢） ===
        "收到一封意外的告白信/匿名礼物": (30, 60, -0.3, 3),
        "走在路上被表白，脸红到宿舍": (30, 60, -0.25, 3),
        "收到意外的红包/礼物": (60, 120, -0.2, 2),
        "论文拿了全班最高分": (60, 120, -0.2, 3),
        "学校公众号推了自己写的文章": (180, 360, -0.2, 2),
        "选修课老师是自己的偶像，激动了一整天": (60, 120, -0.15, 2),
        "接到家里电话，说中了个小奖": (120, 240, -0.2, 2),
        "收到高中同桌寄来的明信片，超感动": (120, 240, -0.15, 2),
        "在武康路偶遇拍照很好看的摄影师，拍了一组写真": (180, 360, -0.2, 2),

        # === 心情不好类（疲劳涨得快） ===
        "论文查重率有点高，头大": (120, 240, 0.2, 2),
        "和室友闹了点小别扭": (120, 240, 0.15, 2),
        "突然下雨没带伞，淋成落汤鸡": (60, 120, 0.2, 1),
        "宿舍热水器坏了，洗了个冷水澡": (60, 120, 0.15, 1),
        "论文又被打回来了，要改": (180, 360, 0.15, 2),
        "小组作业队友不回消息，急死人": (120, 240, 0.15, 2),
        "赶ddl赶了一晚上，手都酸了": (60, 120, 0.3, 3),
        "选课系统又崩了，抢不到课": (60, 120, 0.1, 1),
        "快递丢件了，客服还在扯皮": (120, 240, 0.1, 1),
        "想到毕业就焦虑，不知道找什么工作": (30, 60, 0.1, 2),
        "在看考研学校，头大": (60, 120, 0.15, 2),
        "不知道毕业以后做什么，迷茫": (30, 60, 0.08, 2),
        "实习老板又安排活了，不想干": (120, 240, 0.15, 2),
        "实习同事好讨厌，天天摸鱼还甩锅": (120, 240, 0.15, 2),

        # === 体重焦虑类 ===
        "今天称体重发现重了两斤，心态崩了": (120, 240, 0.15, 1),
        "称体重发现重了两斤，心态崩了": (120, 240, 0.15, 1),
        "忍不住吃了奶茶，减肥失败": (60, 120, 0.1, 1),
        "穿裙子发现腰紧了，emo了": (120, 240, 0.1, 1),
        "买了新衣服，穿上去有点紧": (120, 240, 0.08, 1),

        # === 疲劳高的事件 ===
        "室友半夜打呼噜，没睡好": (60, 120, 0.25, 2),
        "今天没睡好，头有点沉": (60, 120, 0.2, 1),
        "早八上课，灵魂出窍": (120, 180, 0.15, 2),
    }
    for text, score in new_items:
        if text in all_effects:
            min_dur, max_dur, mod, imp = all_effects[text]
            duration = random.randint(min_dur, max_dur)
            _add_effect(text, duration, mod, imp)
        else:
            # 普通事件：默认30分钟~2小时，小事，不影响疲劳涨速
            duration = random.randint(30, 120)
            _add_effect(text, duration, 0, 1)

    if new_items:
        for text, score in new_items:
            _event_pool.append({"text": text, "score": score, "ts": now_ts})
        save_memory()

    if len(_event_pool) > EVENT_POOL_MAX:
        _event_pool.sort(key=lambda e: abs(e["score"]), reverse=True)
        dropped = len(_event_pool) - EVENT_POOL_MAX
        _event_pool[:] = _event_pool[:EVENT_POOL_MAX]
        print(f"✂️ 超出上限，淘汰 {dropped} 条")
        save_memory()

def _get_current_events():
    _refresh_event_pool()
    return sorted(_event_pool, key=lambda e: abs(e["score"]), reverse=True)

def _score_to_mood(score):
    if score >= 7:
        return "元气满满"
    elif score >= 4:
        return "超级开心"
    elif score >= 2:
        return "心情不错"
    elif score >= 0:
        return "心情平平"
    elif score >= -2:
        return "有点累"
    elif score >= -4:
        return "很丧很困"
    else:
        return "崩溃边缘"

def get_mood_and_event(weather_str="", user_id=None):
    holiday = get_today_holiday()

    # 寒暑假日常事件
    break_events = {
        "winter_break": [
            (0, 6, "在家熬夜追剧，爸妈都睡了", 1),
            (6, 10, "在老家睡懒觉，不用早起", 2),
            (10, 12, "在家窝沙发上玩手机", 1),
            (12, 14, "中午吃妈妈做的饭，超好吃", 2),
            (14, 17, "和高中同学约了出门玩", 2),
            (17, 19, "在家帮妈妈做饭", 1),
            (19, 22, "在家看电影，吃零食", 2),
            (22, 24, "躺在床上刷手机，不想开学", -1),
        ],
        "summer_break": [
            (0, 6, "暑假熬夜中，空调吹着超爽", 1),
            (6, 10, "暑假睡懒觉，没人管", 2),
            (10, 12, "在家吹空调追剧", 2),
            (12, 14, "中午吃西瓜，夏天的快乐", 2),
            (14, 17, "实习/兼职中", -1),
            (17, 19, "去图书馆自习，准备考证", 0),
            (19, 22, "晚上出去散步，晚风舒服", 2),
            (22, 24, "暑假余额不足，不想开学", -1),
        ]
    }

    if holiday and holiday.get("type") == "break":
        break_name = "winter_break" if "寒假" in holiday["name"] else "summer_break"
        events_list = break_events.get(break_name, [])
        hour = _current_hour()
        for start_h, end_h, desc, sc in events_list:
            if start_h <= hour < end_h:
                event_desc = desc
                score = sc + holiday.get("mood", 0)
                print(f"🏖️ 寒暑假（{holiday['name']}）：{desc}，心情 {score:+d}")
                # 跳过后面的正常事件逻辑
                if "晴朗" in weather_str or "大部晴朗" in weather_str:
                    score += 1
                elif any(w in weather_str for w in ["雨", "雪", "雾", "阴"]):
                    score -= 1
                fatigue_label, fatigue_score, fatigue_val = get_fatigue_modifier()
                score += fatigue_score
                wallet_label, wallet_score, wallet_ratio = get_wallet_modifier()
                score += wallet_score
                birthday = is_birthday()
                if birthday:
                    score += 2
                events = _get_current_events()
                if events:
                    rand_desc = "；".join(e["text"] for e in events)
                    score += sum(e["score"] for e in events)
                else:
                    rand_desc = "最近没什么特别的事"
                low_items = get_low_consumables()
                if low_items:
                    score -= len(low_items)
                    rand_desc += f"；{','.join(low_items)}快用完了"
                mood = _score_to_mood(score)
                return event_desc, rand_desc, mood, score, fatigue_label, fatigue_val, wallet_label

    if is_sleeping():
        birthday = is_birthday()
        if get_awake_state():
            return "被吵醒后半梦半醒", "无（半清醒中）", "半梦半醒", -2, "困", 0, "睡"
        else:
            base_score = -3 if not birthday else -2
            return "正在睡觉，被消息吵醒，迷迷糊糊", "无（睡觉中）", "迷迷糊糊", base_score, "困", 0, "睡"

    hour = _current_hour()
    current_class = get_current_class()
    late_night = is_late_night_tonight()

    if holiday:
        event_desc = f"放假中（{holiday['name']}）"
        if holiday["_day_index"] == 1:
            event_desc += "（第一天）"
        else:
            event_desc += f"（第 {holiday['_day_index']} 天）"
        score = holiday.get("mood", 2)
        print(f"🎉 节日：{holiday['name']}，第 {holiday['_day_index']} 天，心情 {score:+d}")
    elif current_class:
        note = get_course_note(current_class)
        event_desc = f"正在上{current_class['name']}（{current_class['location']}，{current_class['teacher']}）"
        if note:
            event_desc += f"；课堂状况：{note}"
            print(f"📚 课堂小插曲：{note}")
        score = current_class.get("mood", 0)

        # 上课涨对应科目的知识
        class_name = current_class["name"]
        if _knowledge and class_name in _knowledge.get("study_points", {}):
            old_k = _knowledge["study_points"][class_name]
            new_k = min(100, old_k + 1.5)
            _knowledge["study_points"][class_name] = new_k
            # 知识越高，上课压力越小（心情越好）
            knowledge_boost = int((new_k - 50) / 20)  # 50分以下没加成，50分+1，70分+2，90分+3
            score += knowledge_boost
            if knowledge_boost > 0:
                print(f"📈 {class_name}知识 {old_k:.0f}→{new_k:.0f}，上课更轻松 +{knowledge_boost}")

        print(f"📚 {hour}点 正在上课：{current_class['name']}（{current_class['location']}）")
    elif late_night and (hour >= 23 or hour < 4):
        event_desc = "今晚熬夜，还醒着（在追剧/刷手机/赶作业）"
        score = 2
        print(f"🌙 熬夜中（{hour}点），心情 +2")
    else:
        # 先看有没有正在做的持续事件
        active_task = get_active_task()
        if active_task:
            event_desc = active_task
            # 找这个事件的心情分
            score = 0
            for e in _get_current_events():
                if e["text"] == active_task:
                    score = e["score"]
                    break
            print(f"🔄 正在做：{active_task}")
        else:
            event_desc, score = _get_daily_event_for_hour(hour)

    if "晴朗" in weather_str or "大部晴朗" in weather_str:
        score += 1
    elif any(w in weather_str for w in ["雨", "雪", "雾", "阴"]):
        score -= 1

    fatigue_label, fatigue_score, fatigue_val = "未知", 0, 0
    fatigue_label, fatigue_score, fatigue_val = get_fatigue_modifier()
    score += fatigue_score

    wallet_label, wallet_score, wallet_ratio = get_wallet_modifier()
    score += wallet_score

    birthday = is_birthday()
    if birthday:
        score += 2
        if can_mention_birthday():
            print(f"🎂 今天是她的生日！心情 +2")
        else:
            print(f"🎂 今天是她的生日（已提够次数，不再主动提）")

    events = _get_current_events()
    if events:
        rand_desc = "；".join(e["text"] for e in events)
        score += sum(e["score"] for e in events)
        print(f"🎲 当前小插曲（按|分数|降序）：")
        for e in events:
            print(f"    [{e['score']:+d}] {e['text']}")
    else:
        rand_desc = "最近没什么特别的事"

    # 消耗品低了影响心情
    low_items = get_low_consumables()
    if low_items:
        score -= len(low_items)
        rand_desc += f"；{','.join(low_items)}快用完了"
        print(f"🧴 快用完了：{', '.join(low_items)}")

    # 季节影响
    season_score, season_desc = get_season_mood_effect()
    score += season_score
    if season_score != 0:
        print(f"🍂 季节：{season_desc}，心情 {season_score:+d}")

    # 生理期影响
    period_score, period_desc = get_period_mood_effect()
    score += period_score
    if period_score != 0:
        rand_desc += f"；{period_desc}"
        print(f"🩸 {period_desc}，心情 {period_score:+d}")

    # 体重影响
    if _weight > 52:
        score -= 1
        rand_desc += f"；最近好像胖了，体重{_weight:.1f}kg"
        print(f"⚖️ 体重{_weight:.1f}kg，有点胖了，心情-1")
    elif _weight < 44:
        score -= 1
        rand_desc += f"；最近瘦了好多，体重{_weight:.1f}kg"

    # 考试周影响
    exam, exam_type = is_exam_week()
    if exam:
        score -= 2
        if exam_type == "midterm":
            rand_desc += "；期中复习周，头都大了"
        else:
            rand_desc += "；期末复习周，忙死了"
        print(f"📝 考试周（{exam_type}），心情-2")

    # 实习影响
    if is_internship():
        score -= 1
        rand_desc += "；暑假实习中，上班好累"
        print(f"💼 暑假实习中，心情-1")

    mood = _score_to_mood(score)
    return event_desc, rand_desc, mood, score, fatigue_label, fatigue_val, wallet_label

# =============================================================================
# 【16】工具函数
# =============================================================================
def get_current_time_str(timezone_str=None):
    tz_str = timezone_str or _get_timezone_str()
    try:
        tz = ZoneInfo(tz_str)
        now = datetime.datetime.now(tz)
    except Exception:
        now = datetime.datetime.now()
    weekdays = ['一', '二', '三', '四', '五', '六', '日']
    weekday = weekdays[now.weekday()]
    return now.strftime(f'%Y-%m-%d %H:%M 星期{weekday}')

def get_weather(city=None):
    location = None
    if city:
        location = weather_service.search_city(city)
    if not location:
        location = weather_service.get_location_by_ip()
    if not location:
        location = weather_service.search_city(DEFAULT_CITY)
    if not location:
        return "无法获取位置和天气信息。"

    local_time = weather_service.get_local_time(location['timezone'])
    is_us = location.get('country_code') == 'US'
    weather = weather_service.get_weather_data(
        location['latitude'], location['longitude'], is_fahrenheit=is_us
    )
    if not weather:
        return f"位置：{location['city']}，{location['country']}。当地时间：{local_time}。天气信息获取失败。"

    weather_str = (
        f"位置：{location['city']}，{location['country']}。"
        f"当地时间：{local_time}。"
        f"当前温度：{weather['current_temp']}{weather['unit']}，"
        f"风速：{weather['current_wind']} km/h，"
        f"天气状况：{weather['current_desc']}。"
    )
    if weather.get('forecast'):
        weather_str += " 未来三天预报："
        for day in weather['forecast']:
            weather_str += f"{day['date']} {day['temp_min']}~{day['temp_max']}{weather['unit']} {day['desc']}；"
    return weather_str

def download_image_as_base64(url):
    try:
        url = url.replace('&amp;', '&')
        headers = {'User-Agent': 'Mozilla/5.0'}
        resp = requests.get(url, headers=headers, timeout=15)
        if resp.status_code == 200:
            return base64.b64encode(resp.content).decode('utf-8')
        return None
    except Exception as e:
        print(f"下载图片出错: {e}")
        return None

def _is_pure_question(reply, user_prompt):
    """
    判断回复是不是"纯反问代替回答"：
    1. 回复很短（<=8 字）
    2. 回复以问号结尾
    3. 回复去掉问号后和用户消息高度相似（相同字符占比 > 50%）
    """
    r = reply.strip().strip("？?！!。，,")
    u = user_prompt.strip().strip("？?！!。，,")

    if len(r) > 10:
        return False
    if not reply.strip().endswith(("？", "?")):
        return False

    # 相似度判断
    if not r or not u:
        return False
    common = sum(1 for ch in r if ch in u)
    ratio = common / max(len(r), 1)

    return ratio > 0.5

def _clean_reply(reply, user_prompt=""):
    reply = reply.strip()
    reply = re.sub(r'^\s+', '', reply)

    # 清理 qwen3 思考标签 <think>...</think>
    think_match = re.search(r'<think>([\s\S]*?)</think>', reply)
    if think_match:
        reply = reply[think_match.end():]
    else:
        # 只有开标签没闭标签（被截断了），去掉 <think> 开头部分
        reply = re.sub(r'^\s*<think>[\s\S]*$', '', reply)

    # 兜底：如果清理后为空，说明全是思考内容，取原始内容最后 100 字
    if not reply.strip():
        # 从原始回复里去掉 <think> 后取最后一段
        stripped = re.sub(r'<think>[\s\S]*?(</think>|$)', '', reply)
        if stripped.strip():
            reply = stripped
        else:
            # 实在不行，就用原始回复的最后 80 字
            reply = reply[-80:].strip()

    reply = re.sub(r'[（(]\s*(系统|内心|今天：|手头：|近几天：|我记得|现在|你正在|下一节课)[^）)]*[）)]', '', reply)
    reply = re.sub(r'，手头[\d\.]+元[^。]*。?', '', reply)
    reply = re.sub(r'今天已花[\d\.]+元[^。]*。?', '', reply)
    reply = re.sub(r'你(也)?是(我的好朋友)?李欣然[吧啊呀]?[，。！]?', '', reply)

    # 过滤 (状态：xx/100) 等内心参考泄露
    reply = re.sub(r'[（(][^）)]*[/／]\d+[/／]\d+[）)]', '', reply)
    reply = re.sub(r'…{2,}', '…', reply)
    reply = re.sub(r'\.{3,}', '…', reply)
    reply = re.sub(r'～{2,}', '～', reply)
    reply = re.sub(r'~{2,}', '～', reply)

    reply = re.sub(r'\n\s*\n', '\n', reply)
    reply = re.sub(r'^[，。！？\s]+', '', reply)

    # ★ 兜底：纯反问代替回答 → 替换为"在做自己的事"
    if user_prompt and _is_pure_question(reply, user_prompt):
        print(f"⚠️ 检测到纯反问回复，替换: '{reply}'")
        reply = "在做自己的事"

    reply = reply.replace("主人", "你")

    # 拦截空泛提问：如果回复最后一条消息是空泛问句，删掉它
    BANNED_QUESTIONS = [
        r'你最近在忙什么', r'你最近有啥', r'你最近怎么样',
        r'你平时喜欢', r'你有什么爱好', r'你有啥新鲜事',
        r'今天过得怎么样', r'有什么有趣的', r'有什么事吗',
        r'你呢[？?]?$',
    ]
    lines = reply.split('\n')
    if len(lines) >= 2:
        last = lines[-1].strip()
        for pat in BANNED_QUESTIONS:
            if re.search(pat, last):
                print(f'⚠️ 拦截空泛提问: "{last}"')
                lines.pop()
                break
        reply = '\n'.join(lines)

    reply = reply.strip()
    return reply

# =============================================================================
# 【17】核心对话逻辑
# =============================================================================
def ask_ollama(user_id, prompt, image_base64=None, is_proactive=False):
    if user_id not in chat_histories:
        chat_histories[user_id] = [{"role": "system", "content": SYSTEM_PROMPT}] + FEW_SHOT_EXAMPLES

    if len(chat_histories[user_id]) > MAX_HISTORY_LEN:
        # 始终保留 system + 完整 few-shot，只裁剪真实对话部分
        few_shot_end = 1 + len(FEW_SHOT_EXAMPLES)
        real_messages = chat_histories[user_id][few_shot_end:]
        max_real = MAX_HISTORY_LEN - few_shot_end
        if len(real_messages) > max_real:
            real_messages = real_messages[-max_real:]
        chat_histories[user_id] = chat_histories[user_id][:few_shot_end] + real_messages

    _refresh_bot_dynamic()

    time_str = get_current_time_str()
    weather_str = get_weather()
    short_weather = weather_str[:70]
    event_desc, rand_desc, mood_label, score, fatigue_label, fatigue_val, wallet_label = get_mood_and_event(short_weather, user_id=user_id)
    self_memory_str, user_memory_str = get_memory_str(user_id)
    aff_val = affinity.get(user_id, 10)
    aff_desc, _ = _get_affinity_level(aff_val)
    wallet_str = get_wallet_str()
    history_str = get_recent_history_str()
    birthday = is_birthday()
    holiday = get_today_holiday()
    late_night = is_late_night_tonight()

    next_cls = get_next_class()
    next_cls_str = ""
    if next_cls:
        next_cls_str = f"下一节课：{next_cls['name']}（{next_cls['start']}，{next_cls['location']}）；"

    sleeping = is_sleeping()
    awake = get_awake_state() is not None if sleeping else False

    print(f"[现实时间] {time_str} (TZ={_get_timezone_str()})")
    print(f"[心情系统] 事件: {event_desc} | 心情: {mood_label} ({score}分) | 疲劳: {fatigue_label} ({fatigue_val:.0f}/100) | 钱包: {wallet_label}")
    if late_night:
        print(f"🌙 今晚熬夜日")
    if holiday:
        print(f"🎉 今日节日：{holiday['name']}（第 {holiday['_day_index']} 天）")
    if birthday:
        print(f"🎂 今天是她的生日！")
    print(f"[她的自我认知] {self_memory_str[:100]}...")
    print(f"[关于对方] {user_memory_str}")
    print(f"[钱包] {wallet_str}")
    print(f"[近几天] {history_str}")
    if next_cls:
        print(f"[下一节课] {next_cls['name']}（{next_cls['start']}，{next_cls['location']}）")
    if sleeping:
        print(f"😴 当前处于睡眠时段（{'半清醒' if awake else '刚被吵醒'}）")

    holiday_str = ""
    if holiday:
        holiday_str = f"今天：{holiday['name']}（第 {holiday['_day_index']} 天，共 {holiday.get('days', 1)} 天）；{holiday.get('note', '')}；"

    if birthday and can_mention_birthday():
        birthday_str = "（今天是你——李欣然——的生日，9月20日。不是对方的生日！绝对不要祝对方生日快乐。生日只是心情底色，不要主动提，除非对方问起）；"
    else:
        birthday_str = ""
    late_night_str = "今晚熬夜；" if late_night else ""

    env_info = (
        f"（内心参考，勿复述："
        f"{holiday_str}"
        f"{late_night_str}"
        f"现在 {time_str}；"
        f"你正在：{event_desc}；"
        f"{next_cls_str}"
        f"最近的小插曲（仅供背景，不要主动汇报，除非话题自然带到）：{rand_desc}；"
        f"当前心情：{mood_label}；"
        f"疲劳程度：{fatigue_label}（{fatigue_val:.0f}/100）；"
        f"手头（仅供背景）：{wallet_str}；"
        f"近几天（仅供背景）：{history_str}；"
        f"{birthday_str}"
        f"天气：{short_weather}；"
        f"我记得关于我自己：{self_memory_str}；"
        f"我记得关于对方：{user_memory_str}。"
        f"你和对方的关系：{aff_desc}（亲密度 {aff_val:.0f}/100）。"
        f"★ 回话铁律：先回答对方的问题！以上一切只是背景，不是必须说出口的内容。"
        f"★ 如果对方问\"干什么呢\"，你必须先说自己在干什么，不能只反问回去，不能镜像复读。"
        f"如果对方问\"你叫什么\"，你就答\"我叫李欣然\"，不要讲别的。"
        f"疲劳值越高你越没精神、回复越短，但不要直接说数字。"
        f"钱紧张时说话会更抠一点，会念叨\"这个月快没钱了\"。"
        f"{'今天是节日，可以自然提到。' if holiday else ''}"
        f"{'今天是你生日，心情特别好。但记住：先回答对方的问题，生日只在合适的时候自然带出。' if birthday else ''}"
        f"不要主动找话题！对方说什么就接什么，短消息就短回复，不要硬编今天的生活。"
        f"少用省略号\"…\"和波浪线\"～\"，一条回复最多各 1 个。"
        f"以上场景只供参考，不要硬套！现在没在上课就不要说在上课。"
        f"说话要像真人发微信，短句、随意、有情绪，不要书面语不要鸡汤。）"
    )

    if is_proactive:
        extra = ""
        # 优先根据当前事件生成主动消息
        active_task = get_active_task()
        if active_task:
            # 根据事件类型生成不同的主动消息
            if "ddl" in active_task or "作业" in active_task:
                extra = f"你正在「{active_task}」，写不动了，想找朋友吐槽一下。"
            elif "告白" in active_task or "表白" in active_task or "礼物" in active_task:
                extra = f"你刚「{active_task}」，超开心，想跟朋友分享这个好消息。"
            elif "论文" in active_task or "查重" in active_task:
                extra = f"你「{active_task}」，头大，想找朋友抱怨一下。"
            elif "咖啡" in active_task or "奶茶" in active_task:
                extra = f"你刚「{active_task}」，精神了点，想找朋友随便聊聊。"
            elif "室友" in active_task:
                extra = f"你「{active_task}」，有点烦，想找人吐槽一下。"
            elif "考研" in active_task or "毕业" in active_task or "焦虑" in active_task:
                extra = f"你「{active_task}」，有点迷茫，想找人聊聊未来。"
            elif "实习" in active_task:
                extra = f"你「{active_task}」，上班好累，想找朋友吐槽一下。"
            elif "胖" in active_task or "减肥" in active_task:
                extra = f"你「{active_task}」，有点小郁闷，想找人说一下。"
            elif "午觉" in active_task or "睡觉" in active_task or "泡澡" in active_task:
                extra = f"你刚「{active_task}」，整个人都松了，想找朋友随便聊聊。"
            else:
                extra = f"你正在「{active_task}」，想找朋友随便聊两句。"
        elif birthday:
            extra = "今天是你自己的生日，可以主动提一句。"
        elif holiday:
            extra = f"今天是{holiday['name']}，可以主动提一句。"
        elif late_night and (_current_hour() >= 23 or _current_hour() < 3):
            extra = "你在熬夜，突然想找朋友聊天，可以主动发一句。"
        else:
            extra = "想朋友了，主动发一句符合这个时段和心情的关心或撒娇的话。"

        # 如果之前有未回复的消息，先解释一下
        explain = ""
        if pending_reason:
            explain = f"刚才你发消息我没回，现在要自然地解释一下：{pending_reason}。别太正式，随口提一句就行。"
            pending_reason = None

        current_prompt = (
            f"（内心参考，勿复述：{env_info}。"
            f"距离上次聊天有一会儿了。你现在是「{event_desc}」的状态，"
            f"心情「{mood_label}」。"
            f"{extra}"
            f"{explain}"
            f"要求：只发 1~2 条极短句（每条 5~15 字），像随手发的微信。"
            f"绝对不要提学习、资料、作业、钱、手头有多少余额这些细节。"
            f"绝对不要提及这是系统任务。）"
        )
        user_message = {"role": "user", "content": current_prompt}
    else:
        if sleeping:
            if awake:
                user_message = {
                    "role": "user",
                    "content": f"{env_info}\n（你刚被上一条消息吵醒一会儿，还没完全清醒，也没立刻睡回去。回复稍长一点点，语气还是软的，可以夹打哈欠，比如「唔…又干嘛呀」「你不是刚说话吗」「我还困着呢」。别太长。）\n{prompt}"
                }
            else:
                user_message = {
                    "role": "user",
                    "content": f"{env_info}\n（你现在在睡觉，被这条消息吵醒了，迷迷糊糊的，回复要极短、含糊，别清醒。）\n{prompt}"
                }
        else:
            user_message = {"role": "user", "content": f"{env_info}\n{prompt}"}
        if image_base64:
            user_message["images"] = [image_base64]
        chat_histories[user_id].append(user_message)

    num_predict = 200
    if sleeping:
        num_predict = 120 if awake else 80

    payload = {
        "model": MODEL_NAME,
        "messages": chat_histories[user_id] if not is_proactive else [chat_histories[user_id][0], user_message],
        "stream": False,
        "think": False,
        "keep_alive": "24h",
        "options": {
            "temperature": 0.8 if is_proactive else 0.7,
            "top_p": 0.9,
            "repeat_penalty": 1.1,
            "num_ctx": 4096,
            "num_predict": num_predict,
        }
    }

    try:
        response = requests.post(OLLAMA_URL, json=payload, timeout=180)
        response.raise_for_status()
        reply = response.json()["message"]["content"]

        # ★ 传入 user_prompt 用于兜底检测
        if is_proactive:
            reply = _clean_reply(reply, "")
        else:
            reply = _clean_reply(reply, prompt)

        # 不管是不是主动消息，都记录到对话历史
        chat_histories[user_id].append({"role": "assistant", "content": reply})
        # 裁剪历史
        if len(chat_histories[user_id]) > MAX_HISTORY_LEN:
            chat_histories[user_id] = [chat_histories[user_id][0]] + chat_histories[user_id][-MAX_HISTORY_LEN+1:]
        save_chat_history()
        return reply
    except Exception as e:
        print(f"请求 Ollama 失败: {e}")
        return None

# =============================================================================
# 【18】骚扰消息生成
# =============================================================================
NUISANCE_FALLBACKS = [
    "在干嘛", "嘿", "喂", "诶", "无聊", "睡了没",
    "在不在", "理我一下", "突然想你了", "你干嘛呢",
    "唔", "哈喽", "我饿了", "烦死了", "好无聊啊",
]

def ask_nuisance(user_id):
    if user_id not in chat_histories:
        chat_histories[user_id] = [{"role": "system", "content": SYSTEM_PROMPT}] + FEW_SHOT_EXAMPLES

    time_str = get_current_time_str()
    weather_str = get_weather()
    short_weather = weather_str[:70]
    event_desc, rand_desc, mood_label, score, fatigue_label, fatigue_val, wallet_label = get_mood_and_event(short_weather, user_id=user_id)

    hour = _current_hour()
    late_night = is_late_night_tonight()

    if late_night and (hour >= 23 or hour < 3):
        style_hint = "你在熬夜，有点无聊或者困但睡不着，可以撒娇或者卖惨。"
    elif 6 <= hour < 10:
        style_hint = "你刚醒或者还在床上，迷迷糊糊的。"
    elif 12 <= hour < 14:
        style_hint = "你刚吃完饭犯困。"
    elif 20 <= hour < 23:
        style_hint = "你在宿舍刷手机，突然想找朋友说话。"
    else:
        style_hint = "你突然想起对方，想发个消息。"

    prompt = (
        f"（内心参考，勿复述："
        f"现在 {time_str}；"
        f"你正在：{event_desc}；"
        f"当前心情：{mood_label}；"
        f"疲劳：{fatigue_label}。"
        f"{style_hint}"
        f"要求：只发 1 条极短消息，最长 15 个字，像随手发的微信。"
        f"例如：「在干嘛」「嘿」「无聊」「喂」「睡了没」。"
        f"绝对不要提学习、钱、作业、上课。"
        f"绝对不要问\"有什么需要帮忙的吗\"这种客服话。"
        f"绝对不要提及这是系统任务。）"
    )

    payload = {
        "model": MODEL_NAME,
        "messages": [
            chat_histories[user_id][0],
            {"role": "user", "content": prompt},
        ],
        "stream": False,
        "think": False,
        "keep_alive": "24h",
        "options": {
            "temperature": 0.85,
            "top_p": 0.9,
            "repeat_penalty": 1.1,
            "num_ctx": 4096,
            "num_predict": 30,
        }
    }

    try:
        response = requests.post(OLLAMA_URL, json=payload, timeout=60)
        response.raise_for_status()
        reply = response.json()["message"]["content"]
        reply = _clean_reply(reply, "")

        if len(reply) > NUISANCE_MAX_LEN:
            reply = reply[:NUISANCE_MAX_LEN]

        if not reply:
            reply = random.choice(NUISANCE_FALLBACKS)

        return reply
    except Exception as e:
        print(f"骚扰消息生成失败: {e}")
        return random.choice(NUISANCE_FALLBACKS)

# =============================================================================
# 【19】消息发送
# =============================================================================
async def send_msg(websocket, message_type, user_id, group_id, text):
    send_payload = {
        "action": "send_msg",
        "params": {
            "message_type": message_type,
            "user_id": user_id,
            "group_id": group_id,
            "message": text
        }
    }
    await websocket.send(json.dumps(send_payload))

async def send_multi_msg(websocket, message_type, user_id, group_id, text):
    parts = [p.strip() for p in text.split("\n") if p.strip()]
    if not parts:
        return

    if len(parts) == 1:
        single = parts[0]
        m = list(re.finditer(r'[，。？！~…]', single))
        if len(m) >= 1 and len(single) >= 10:
            idx = m[len(m) // 2].end()
            parts = [single[:idx].strip(), single[idx:].strip()]

    # 计算打字速度倍率：疲劳越高越慢，亲密度越高越快
    fatigue_label, _, fatigue_val = get_fatigue_modifier()
    aff_val = affinity.get(user_id, 10)
    speed_mult = 1.0
    if fatigue_val > 60:
        speed_mult *= 1.5  # 很累，打字慢
    elif fatigue_val > 40:
        speed_mult *= 1.2
    if aff_val > 60:
        speed_mult *= 0.8  # 熟了，打字快
    elif aff_val < 20:
        speed_mult *= 1.1  # 刚认识，犹豫一下

    sent_msgs = []
    for i, part in enumerate(parts):
        if not part:
            continue
        delay = min(max(len(part) * 0.1, 0.8), 3.0) + random.uniform(0.3, 1.0)
        delay *= speed_mult
        if is_sleeping():
            delay *= 2
        await asyncio.sleep(delay)
        msg_id = await send_msg(websocket, message_type, user_id, group_id, part)
        if msg_id:
            sent_msgs.append(msg_id)
        if i < len(parts) - 1:
            await asyncio.sleep(random.uniform(0.5, 1.5))

    # 从她的回复里提取关于自己的重要信息
    extract_bot_self_memory(text)

    # 偶尔撤回最后一条（5%概率）
    if sent_msgs and random.random() < 0.05:
        await asyncio.sleep(random.uniform(2, 5))
        try:
            await websocket.send(json.dumps({
                "action": "delete_msg",
                "params": {"message_id": sent_msgs[-1]}
            }))
            print(f"↩️ 撤回了一条消息")
        except Exception as e:
            print(f"撤回失败: {e}")

# =============================================================================
# 【20】消息接收与处理
# =============================================================================
async def handle_message(websocket, message_data):
    if message_data.get("post_type") != "message":
        return

    user_id = message_data.get("user_id")
    message_type = message_data.get("message_type")
    raw_message = message_data.get("raw_message", "").strip()
    group_id = message_data.get("group_id")

    if message_type == "private" and user_id == MASTER_QQ:
        last_interaction_time[user_id] = _now_ts()

    print(f"收到消息 [{user_id}]: {raw_message}")

    # 私聊命令处理
    if message_type == "private" and user_id == MASTER_QQ:
        # /状态 命令
        if raw_message == "/状态" or raw_message == "/status":
            _, _, fatigue_val = get_fatigue_modifier()
            event_desc, _, mood_label, score, _, _, _ = get_mood_and_event(weather_str="", user_id=user_id)

            # 当前活跃事件
            active_texts = []
            for e in _active_effects:
                remaining = (e["start_ts"] + e["duration_sec"]) - _now_ts()
                if remaining > 0:
                    active_texts.append(f"{e['text']}（还剩{int(remaining//60)}分钟）")

            wallet = load_json("data/wallet.json")
            balance = wallet.get("balance", 0)

            aff = affinity.get(user_id, 10)

            reply = f"""📊 当前状态
---
正在做：{event_desc}
心情：{mood_label}（{score:+d}）
疲劳：{fatigue_val:.0f}/100
余额：{balance:.1f}元
亲密度：{aff:.0f}/100
---
活跃事件：
"""
            if active_texts:
                for t in active_texts:
                    reply += "  • " + t + "\n"
            else:
                reply += "  （无）\n"

            if is_sleeping():
                reply += "\n😴 正在睡觉"

            await send_multi_msg(websocket, message_type, user_id, group_id, reply)
            return

        # /事件 命令 - 列出所有互斥组
        if raw_message == "/事件" or raw_message == "/events":
            reply = "📋 事件互斥组\n---\n"
            for group_name, events in EFFECT_GROUPS.items():
                group_cn = {"rest": "🛌 休息组", "study": "📚 学习组", "outdoor": "🚶 出门组"}.get(group_name, group_name)
                reply += "\n" + group_cn + "：\n"
                for e in events:
                    reply += "  • " + e + "\n"
            await send_multi_msg(websocket, message_type, user_id, group_id, reply)
            return

        # /疲劳 命令 - 设置疲劳值
        if raw_message.startswith("/疲劳"):
            try:
                val = int(raw_message.split()[1])
                global fatigue
                fatigue = max(0, min(100, val))
                await send_multi_msg(websocket, "private", user_id, None, f"✅ 疲劳值设为 {fatigue:.0f}")
            except:
                await send_multi_msg(websocket, "private", user_id, None, "用法：/疲劳 80")
            return

        # /亲密度 命令 - 设置亲密度
        if raw_message.startswith("/亲密度"):
            try:
                val = int(raw_message.split()[1])
                affinity[user_id] = max(0, min(100, val))
                await send_multi_msg(websocket, "private", user_id, None, f"✅ 亲密度设为 {affinity[user_id]:.0f}")
            except:
                await send_multi_msg(websocket, "private", user_id, None, "用法：/亲密度 80")
            return

        # /触发 命令 - 手动触发一个事件
        if raw_message.startswith("/触发"):
            try:
                event_text = raw_message.split(" ", 1)[1]
                _add_effect(event_text, 60, 0, 1)
                await send_multi_msg(websocket, "private", user_id, None, f"✅ 触发事件：{event_text}")
            except Exception as e:
                await send_multi_msg(websocket, "private", user_id, None, "用法：/触发 事件名\n错误：" + str(e))
            return

        # /随机事件 命令 - 随机触发一个事件
        if raw_message == "/随机事件":
            import random as r
            all_events = [item[0] for item in RANDOM_EVENTS]
            ev = r.choice(all_events)
            _add_effect(ev, r.randint(30, 120), 0, 1)
            await send_multi_msg(websocket, "private", user_id, None, f"✅ 随机触发：{ev}")
            return

        # /待回复 命令 - 查看待回复队列
        if raw_message == "/待回复":
            if not pending_replies:
                await send_multi_msg(websocket, "private", user_id, None, "📭 没有待回复的消息")
            else:
                reply = "📬 待回复队列（" + str(len(pending_replies)) + "条）：\n"
                for pr in pending_replies:
                    remaining = (pr["reply_after"] - _now_ts()) / 60
                    reply += "  • " + pr['message'][:20] + "... | " + pr['reason_detail'] + " | 还剩" + str(int(remaining)) + "分钟\n"
                await send_multi_msg(websocket, "private", user_id, None, reply)
            return

        # /清空 命令 - 清空待回复队列
        if raw_message == "/清空":
            pending_replies.clear()
            await send_multi_msg(websocket, "private", user_id, None, "✅ 已清空待回复队列")
            return

    if message_type == "group":
        if not raw_message.startswith("/ai "):
            return
        raw_message = raw_message.replace("/ai ", "", 1)

    sleeping = is_sleeping()
    if sleeping:
        if not should_wake_up():
            print(f"😴 完全没被吵醒，本条不回复")
            return
        print(f"😴 被吵醒了，准备回复")

    start_time = _now_ts()

    image_base64 = None
    base64_match = re.search(r'\[CQ:image,.*?base64://(.*?)\]', raw_message)
    if base64_match:
        image_base64 = base64_match.group(1)
    else:
        img_match = re.search(r'\[CQ:image,.*?url=(.*?)\]', raw_message)
        if img_match:
            img_url = img_match.group(1).replace('&amp;', '&')
            image_base64 = download_image_as_base64(img_url)

    raw_message = re.sub(r'\[CQ:image,.*?\]', '', raw_message).strip()
    if not raw_message:
        raw_message = "看看这张图~"

    if raw_message and raw_message != "看看这张图~":
        extract_memory(user_id, raw_message)

    # 每次聊天增加亲密度
    # 记录第一次聊天日期
    if user_id not in _first_chat_date:
        _first_chat_date[user_id] = _today_str()
        print(f"📅 第一次聊天：{_first_chat_date[user_id]}")

    add_affinity(user_id, 0.5)

    # 偶尔已读不回（疲劳/心情/亲密度/睡觉都影响）
    _, _, fatigue_val = get_fatigue_modifier()
    ignore_chance = 0.0

    # 疲劳基础
    if fatigue_val > 70:
        ignore_chance += 0.15
    elif fatigue_val > 50:
        ignore_chance += 0.05

    # 心情影响（心情差更不想回）
    _, _, _, mood_score, _, _, _ = get_mood_and_event(weather_str="", user_id=user_id)
    if mood_score < -5:
        ignore_chance += 0.1
    elif mood_score < -2:
        ignore_chance += 0.05

    # 忙碌中（洗澡/睡觉/午休），更不想回
    if is_busy_now():
        ignore_chance += 0.4
        print("🚿 忙碌中，不想回消息")

    # 亲密度影响（越熟越愿意回）
    aff_val = affinity.get(user_id, 10)
    if aff_val < 20:
        ignore_chance += 0.1
    elif aff_val > 70:
        ignore_chance -= 0.1

    # 睡觉中
    if is_sleeping():
        ignore_chance += 0.3

    # 上限：最多50%概率不回
    ignore_chance = max(0, min(0.5, ignore_chance))

    if random.random() < ignore_chance:
        print(f"😴 已读不回（疲劳{fatigue_val:.0f}）")

        # 判断原因，决定多久后回复
        if is_sleeping():
            reason = "sleeping"
            reason_detail = "睡着了"
            reply_delay_min = random.randint(30, 90)  # 半小时到一个半小时后醒了回
        elif is_busy_now():
            reason = "busy"
            reason_detail = "在忙"
            # 找当前事件剩余时间
            busy_remaining = 0
            for e in _active_effects:
                remaining = (e["start_ts"] + e["duration_sec"]) - _now_ts()
                if remaining > 0 and e["importance"] >= 2:
                    busy_remaining = max(busy_remaining, remaining)
            reply_delay_min = max(10, int(busy_remaining / 60))  # 事件结束后回
        elif fatigue_val > 70:
            reason = "tired"
            reason_detail = "太累了"
            reply_delay_min = random.randint(30, 60)  # 半小时到一小时后缓过来了
        elif mood_score < -5:
            reason = "mood"
            reason_detail = "心情差"
            reply_delay_min = random.randint(20, 40)  # 20~40分钟后心情好点了
        else:
            reason = "distracted"
            reason_detail = "走神了"
            reply_delay_min = random.randint(10, 20)  # 10~20分钟后看到了

        # 记录未回复原因，下次主动消息解释
        global pending_reason
        if reason == "sleeping":
            pending_reason = "刚才睡着了，没看到"
        elif reason == "busy":
            pending_reason = "刚才在忙，没看到消息"
        elif reason == "tired":
            pending_reason = "刚才太累了，眯了一会儿"
        elif reason == "mood":
            pending_reason = "刚才有点emo，没心情回"
        else:
            pending_reason = "刚才走神了，没看到消息"

        # 加入待回复队列
        pending_replies.append({
            "user_id": user_id,
            "message": raw_message,
            "reason": reason,
            "reason_detail": reason_detail,
            "reply_after": _now_ts() + reply_delay_min * 60,
            "delay_min": reply_delay_min,
        })
        print(f"⏰ 已加入待回复队列，{reply_delay_min}分钟后回（原因：{reason_detail}）")

        # 即使已读不回，也要把用户消息记录下来，这样下次聊天能知道之前说过什么
        if user_id in chat_histories:
            chat_histories[user_id].append({"role": "user", "content": raw_message})
            # 裁剪历史
            if len(chat_histories[user_id]) > MAX_HISTORY_LEN:
                chat_histories[user_id] = [chat_histories[user_id][0]] + chat_histories[user_id][-MAX_HISTORY_LEN+1:]
            save_chat_history()
        return

    reply_text = ask_ollama(user_id, raw_message, image_base64)

    elapsed_time = _now_ts() - start_time
    print(f"⏱️ Ollama 生成耗时: {elapsed_time:.2f} 秒")

    if not reply_text:
        return

    reply_text = reply_text.strip()
    reply_text = re.sub(r'^\s+', '', reply_text)

    if len(reply_text) > 1500:
        reply_text = reply_text[:1500] + "\n...(回复过长已截断)"

    if sleeping:
        mark_awake()
        _clear_sleep_state()

    await send_multi_msg(websocket, message_type, user_id, group_id, reply_text)

# =============================================================================
# 【21】主动消息后台任务
# =============================================================================
async def proactive_loop(websocket):
    global _next_proactive_time
    _next_proactive_time = _now_ts() + random.randint(PROACTIVE_COOLDOWN_MIN, PROACTIVE_COOLDOWN_MAX)
    print(f"💤 主动消息任务已启动（冷却 {PROACTIVE_COOLDOWN_MIN}s ~ {PROACTIVE_COOLDOWN_MAX}s 随机）")

    while True:
        try:
            await asyncio.sleep(PROACTIVE_INTERVAL)
            now = _now()
            now_ts = _now_ts()

            # 检查待回复队列
            if pending_replies:
                for i in range(len(pending_replies) - 1, -1, -1):
                    pr = pending_replies[i]
                    should_reply = False

                    # 到时间了，该回复了
                    if now_ts >= pr["reply_after"]:
                        should_reply = True
                    # 如果现在正在看手机（触发了刷手机/刷抖音事件），提前回复
                    elif any("刷" in e["text"] or "手机" in e["text"] or "摸鱼" in e["text"] for e in _active_effects):
                        should_reply = True
                        print(f"📱 正在看手机，提前回复")

                    if should_reply:
                        user_id = pr["user_id"]
                        reason = pr["reason"]
                        reason_detail = pr["reason_detail"]

                        # 如果现在在睡觉，再等等
                        if is_sleeping():
                            pr["reply_after"] = now_ts + 30 * 60  # 再等半小时
                            continue

                        print(f"⏰ 回复之前的消息（原因：{reason_detail}）")

                        # 生成回复，带解释
                        reply_text = ask_ollama(user_id, pr["message"], is_proactive=False)
                        if reply_text:
                            reply_text = reply_text.strip()
                            await send_multi_msg(websocket, "private", user_id, None, reply_text)
                            last_interaction_time[user_id] = _now_ts()
                            print(f"📤 延迟回复: {reply_text}")

                        # 从队列里删掉
                        del pending_replies[i]

            # 正常活跃时间内才主动发
            is_active_hour = ACTIVE_HOUR_START <= now.hour < ACTIVE_HOUR_END
            # 熬夜的时候，10%概率也主动发
            is_late_night = (now.hour >= 23 or now.hour < 2) and is_late_night_tonight()

            if not is_active_hour:
                if is_late_night:
                    # 熬夜的时候，10%概率主动发
                    if random.random() > 0.1:
                        continue
                else:
                    continue

            if is_sleeping():
                continue

            if now_ts < _next_proactive_time:
                continue

            if MASTER_QQ in last_interaction_time:
                time_since_last = now_ts - last_interaction_time[MASTER_QQ]
                if time_since_last > PROACTIVE_COOLDOWN_MIN:
                    print("✨ 触发主动消息！")
                    proactive_text = ask_ollama(MASTER_QQ, "", is_proactive=True)
                    if proactive_text:
                        proactive_text = proactive_text.strip()
                        await send_multi_msg(websocket, "private", MASTER_QQ, None, proactive_text)
                        last_interaction_time[MASTER_QQ] = _now_ts()
                        print(f"📤 已发送主动消息: {proactive_text}")
                        _next_proactive_time = now_ts + random.randint(PROACTIVE_COOLDOWN_MIN, PROACTIVE_COOLDOWN_MAX)
                        wait_min = (_next_proactive_time - now_ts) / 60
                        print(f"⏰ 下次主动消息将在 {wait_min:.0f} 分钟后")
            else:
                last_interaction_time[MASTER_QQ] = now_ts

        except Exception as e:
            print(f"主动消息任务出错: {e}")
            await asyncio.sleep(10)

# =============================================================================
# 【22】骚扰消息后台任务
# =============================================================================
async def nuisance_loop(websocket):
    global _next_nuisance_time
    _next_nuisance_time = _now_ts() + random.randint(NUISANCE_COOLDOWN_MIN, NUISANCE_COOLDOWN_MAX)

    if not ENABLE_NUISANCE:
        print(f"😜 骚扰系统已关闭")
        return

    print(f"😜 骚扰系统已启动（冷却 {NUISANCE_COOLDOWN_MIN}s ~ {NUISANCE_COOLDOWN_MAX}s）")

    while True:
        try:
            await asyncio.sleep(NUISANCE_CHECK_INTERVAL)

            now = _now()
            now_ts = _now_ts()

            if is_sleeping():
                continue

            hour = now.hour
            if not (7 <= hour or hour < 3):
                continue

            if now_ts < _next_nuisance_time:
                continue

            if random.random() > NUISANCE_CHANCE_PER_CHECK:
                continue

            print("😜 触发骚扰消息！")
            text = ask_nuisance(MASTER_QQ)
            if text:
                text = text.strip()
                await send_multi_msg(websocket, "private", MASTER_QQ, None, text)
                last_interaction_time[MASTER_QQ] = now_ts
                print(f"📤 已发送骚扰: {text}")

            _next_nuisance_time = now_ts + random.randint(NUISANCE_COOLDOWN_MIN, NUISANCE_COOLDOWN_MAX)
            wait_min = (_next_nuisance_time - now_ts) / 60
            print(f"⏰ 下次骚扰将在 {wait_min:.0f} 分钟后")

        except Exception as e:
            print(f"骚扰任务出错: {e}")
            await asyncio.sleep(30)

# =============================================================================
# 【23】时区同步后台任务
# =============================================================================
async def timezone_sync_loop():
    print(f"🌍 时区同步任务已启动（每 {TIMEZONE_SYNC_INTERVAL // 60} 分钟）")
    while True:
        try:
            await asyncio.sleep(TIMEZONE_SYNC_INTERVAL)
            sync_timezone_from_location()
        except Exception as e:
            print(f"时区同步出错: {e}")
            await asyncio.sleep(60)

# =============================================================================
# 【24】主程序
# =============================================================================
async def main():
    load_events()
    load_courses()
    load_memory()
    load_wallet()
    load_history()
    load_holidays()
    load_chat_history()

    print("📅 从API获取真实节假日...")
    global _api_holidays
    _api_holidays = fetch_holidays_from_api()

    print("🌍 启动时区同步...")
    if not sync_timezone_from_location():
        print(f"⚠️ 定位失败，使用 fallback 时区：{BOT_TIMEZONE}")
    print(f"✅ 当前现实时区：{_get_timezone_str()}")
    print(f"🕐 当前现实时间：{_now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"👧 她的固定人设：{len(bot_fixed_memory)} 条 | 动态信息：{len(bot_dynamic_memory)} 条")
    print(f"📚 课程：{'启用' if COURSE_SCHEDULE else '停用'}")

    _get_sleep_hours_today()

    holiday = get_today_holiday()
    if holiday:
        print(f"🎉 今天是 {holiday['name']}（第 {holiday['_day_index']} 天）")
    if is_birthday():
        print(f"🎂 今天是李欣然的生日！")

    print("正在连接 QQ 协议端...")
    async with websockets.connect(WS_URL, ping_interval=None, ping_timeout=None) as websocket:
        print("连接成功！机器人已启动，等待消息...")

        asyncio.create_task(proactive_loop(websocket))
        asyncio.create_task(nuisance_loop(websocket))
        asyncio.create_task(timezone_sync_loop())
        asyncio.create_task(world_tick_loop())

        while True:
            try:
                message = await websocket.recv()
                data = json.loads(message)
                asyncio.create_task(handle_message(websocket, data))
            except websockets.exceptions.ConnectionClosed:
                print("连接断开，尝试重连...")
                break

if __name__ == "__main__":
    while True:
        try:
            asyncio.run(main())
        except KeyboardInterrupt:
            print("程序已手动退出。")
            break
        except Exception as e:
            print(f"连接出现异常，5秒后重连... 错误信息: {e}")
            time.sleep(5)