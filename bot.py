"""Telegram-бот: видео, конвертер, QR, погода, утренняя карточка, правда или действие в личке; игры, казино, мафия и анонимные вопросы в группах."""
import asyncio
import hashlib
import html
import importlib
import io
import json
import logging
import math
import os
import random
import re
import secrets
import shutil
import sys
import tempfile
import time as time_module
import zipfile
from collections import defaultdict
from datetime import datetime, time, timedelta
from pathlib import Path
from urllib.parse import parse_qs, quote, urlparse
from zoneinfo import ZoneInfo

import feedparser
import httpx
import qrcode
import yt_dlp
from dotenv import load_dotenv
from PIL import Image, ImageOps
from telegram import (BotCommand, BotCommandScopeAllGroupChats, BotCommandScopeChat, InlineKeyboardButton,
                      InlineKeyboardMarkup, InlineQueryResultCachedAudio, InlineQueryResultCachedVideo,
                      InlineQueryResultsButton, ReplyKeyboardMarkup, Update)
from telegram.ext import (
    Application, ApplicationHandlerStop, CallbackQueryHandler, ChatMemberHandler, CommandHandler,
    ContextTypes, InlineQueryHandler, MessageHandler, TypeHandler, filters,
)

load_dotenv()
BOT_TOKEN = os.environ["BOT_TOKEN"]
OWNER_ID = int(os.environ["OWNER_ID"])          # владелец: без лимитов, все команды
CITY = os.getenv("CITY", "Москва")
FRIEND_CITY = os.getenv("FRIEND_CITY", "Москва")    # город друзей по умолчанию
MORNING_TIME = os.getenv("MORNING_TIME", "08:00")
TZ = ZoneInfo(os.getenv("TZ", "Europe/Moscow"))
LOCAL_API_URL = os.getenv("LOCAL_API_URL")       # напр. http://localhost:8081 (снимает лимит до 2 ГБ)
MAX_UPLOAD = (1900 if LOCAL_API_URL else 49) * 1024 * 1024   # макс. размер одного файла


def _ids(raw: str | None) -> set[int]:
    return {int(x) for x in re.split(r"[,\s;]+", raw or "") if x.lstrip("-").isdigit()}


ENV_ALLOWED = _ids(os.getenv("ALLOWED_IDS"))                   # друзья «навсегда» из настроек Railway
DATA_DIR = Path(os.getenv("DATA_DIR", "data"))                 # для сохранения друзей между перезапусками
STORE = DATA_DIR / "users.json"


def _load_users() -> dict:
    try:
        d = json.loads(STORE.read_text(encoding="utf-8"))
    except Exception:
        d = {}
    return {k: {int(i): n for i, n in d.get(k, {}).items()} for k in ("approved", "blocked", "prefs", "groups")}


USERS = _load_users()                                          # approved / blocked: {id: имя}


def _save_users():
    try:
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        tmp = STORE.with_suffix(".tmp")
        tmp.write_text(json.dumps({k: {str(i): n for i, n in v.items()} for k, v in USERS.items()},
                                  ensure_ascii=False), encoding="utf-8")
        tmp.replace(STORE)
    except Exception:
        log.exception("не удалось сохранить список друзей")


STATS_FILE = DATA_DIR / "stats.json"


def _load_stats() -> dict:
    try:
        d = json.loads(STATS_FILE.read_text(encoding="utf-8"))
    except Exception:
        d = {}
    return {"solo": {int(k): v for k, v in d.get("solo", {}).items()},
            "group": {int(c): {int(u): v for u, v in us.items()} for c, us in d.get("group", {}).items()}}


STATS = _load_stats()        # solo: {uid: {name, wins, games}}, group: {chat: {uid: {name, wins}}}


def _save_stats():
    try:
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        tmp = STATS_FILE.with_suffix(".tmp")
        tmp.write_text(json.dumps({
            "solo": {str(k): v for k, v in STATS["solo"].items()},
            "group": {str(c): {str(u): v for u, v in us.items()} for c, us in STATS["group"].items()},
        }, ensure_ascii=False), encoding="utf-8")
        tmp.replace(STATS_FILE)
    except Exception:
        log.exception("не удалось сохранить таблицу лидеров")


def add_solo_win(uid: int, name: str, game: str):
    name = str(name)
    r = STATS["solo"].setdefault(uid, {"name": name, "wins": 0, "games": {}})
    r["name"] = name
    r["wins"] += 1
    r["games"][game] = r["games"].get(game, 0) + 1
    _save_stats()


def add_group_win(chat_id: int, uid: int, name: str):
    name = str(name)
    r = STATS["group"].setdefault(chat_id, {}).setdefault(uid, {"name": name, "wins": 0})
    r["name"] = name
    r["wins"] += 1
    _save_stats()


def pref(uid: int, key: str) -> bool:
    """Личные настройки: оповещения о дожде и утренняя сводка (по умолчанию включены)."""
    return USERS["prefs"].get(uid, {}).get(key, True)


def subscribers(key: str) -> list[int]:
    ids = {OWNER_ID} | ENV_ALLOWED | set(USERS["approved"])
    return sorted(u for u in ids if pref(u, key))


def is_allowed(uid: int) -> bool:
    return uid == OWNER_ID or uid in ENV_ALLOWED or uid in USERS["approved"]


FRIEND_MAX_MIN = int(os.getenv("FRIEND_MAX_MIN", "30"))        # макс. длина видео для друзей, мин
FRIEND_MAX_MB = int(os.getenv("FRIEND_MAX_MB", "150"))         # макс. размер файла для друзей, МБ
FRIEND_JOBS_PER_HOUR = int(os.getenv("FRIEND_JOBS_PER_HOUR", "6"))   # скачиваний/конвертаций в час
MAX_PARALLEL = int(os.getenv("MAX_PARALLEL", "2"))             # тяжёлых задач одновременно на весь бот
FRIEND_DOMAINS = ("youtube.com", "youtu.be", "tiktok.com", "instagram.com")
Image.MAX_IMAGE_PIXELS = 40_000_000                            # защита от «бомб» в картинках

NEWS_FEEDS = [                                   # можно заменить на любые RSS
    "https://feeds.bbci.co.uk/russian/rss.xml",
    "https://rss.dw.com/xml/rss-ru-all",
]
WEATHER_CODES = {
    0: "ясно ☀️", 1: "малооблачно 🌤", 2: "облачно ⛅", 3: "пасмурно ☁️",
    45: "туман 🌫", 48: "туман 🌫", 51: "морось 🌦", 53: "морось 🌦", 55: "морось 🌦",
    61: "дождь 🌧", 63: "дождь 🌧", 65: "сильный дождь 🌧", 71: "снег 🌨",
    73: "снег 🌨", 75: "сильный снег ❄️", 80: "ливень 🌧", 81: "ливень 🌧",
    82: "сильный ливень ⛈", 95: "гроза ⛈", 96: "гроза с градом ⛈", 99: "гроза с градом ⛈",
}
URL_RE = re.compile(r"https?://\S+")
LINE = "━━━━━━━━━━━━━━"
esc = html.escape
logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger("bot")




# ====================== надёжность: файлы данных, метрики, оповещения, бэкап, yt-dlp ======================
META_FILE = DATA_DIR / "meta.json"
METRICS_FILE = DATA_DIR / "metrics.json"
CACHE_FILE = DATA_DIR / "cache.json"
CUSTOM_FILE = DATA_DIR / "custom_td.json"
START_TIME = time_module.time()
APP_BOT = None                                    # бот приложения: нужен для уведомлений из любых мест


def _load_json(path: Path, default):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return default


def _save_json(path: Path, data):
    try:
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        tmp = path.with_suffix(".tmp")
        tmp.write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")
        tmp.replace(path)
    except Exception:
        log.exception("не удалось сохранить %s", path.name)


META = _load_json(META_FILE, {})
META.setdefault("cheques", {})                    # подарочные чеки: token -> {from, amount, t}
META.setdefault("invites", {})                    # приглашённый -> пригласивший
META.setdefault("last_week", "")
META.setdefault("last_month", "")


def _save_meta():
    _save_json(META_FILE, META)


METRICS = _load_json(METRICS_FILE, {"days": {}})
METRICS.setdefault("days", {})
_metrics_dirty = [False]


def metric(name: str, uid: int | None = None):
    day = METRICS["days"].setdefault(datetime.now(TZ).date().isoformat(), {})
    day[name] = day.get(name, 0) + 1
    if uid:
        users = day.setdefault("users", [])
        if uid not in users:
            users.append(uid)
    for old in sorted(METRICS["days"])[:-30]:      # храним последние 30 дней
        METRICS["days"].pop(old, None)
    _metrics_dirty[0] = True


async def flush_metrics(context: ContextTypes.DEFAULT_TYPE):
    if _metrics_dirty[0]:
        _metrics_dirty[0] = False
        _save_json(METRICS_FILE, METRICS)


ALERTS: dict[str, float] = {}


async def notify_owner(bot, text: str, key: str = "x", cooldown: int = 600):
    """Сообщение владельцу; одинаковые (по ключу) не чаще раза в cooldown секунд."""
    now = time_module.time()
    if now - ALERTS.get(key, 0) < cooldown:
        return
    ALERTS[key] = now
    try:
        await bot.send_message(OWNER_ID, text[:3500])
    except Exception:
        log.exception("не удалось написать владельцу")


def notify_user(uid: int, text: str, kb=None):
    """Тихо отправить личное сообщение (если не получится, ничего страшного)."""
    if APP_BOT is None:
        return

    async def _go():
        try:
            await APP_BOT.send_message(uid, text, parse_mode="HTML", reply_markup=kb)
        except Exception:
            pass
    spawn(_go())


async def on_error(update: object, context: ContextTypes.DEFAULT_TYPE):
    err = context.error
    log.error("необработанная ошибка", exc_info=err)
    name = type(err).__name__
    if name in ("NetworkError", "TimedOut", "RetryAfter", "BadRequest", "Conflict"):       # сетевые мелочи не шлём
        return
    metric("errors")
    await notify_owner(context.bot, f"⚠️ Ошибка в боте: {name}: {str(err)[:300]}", key=f"err:{name}")


def explain_error(text: str) -> tuple[str, bool]:
    """Понятное объяснение ошибки скачивания и признак, что стоит предупредить владельца."""
    low = text.lower()
    if "not a bot" in low or "confirm you" in low or "sign in" in low and "youtube" in low:
        return "YouTube сейчас не отдаёт видео этому серверу. Я сообщил владельцу, попробуйте позже.", True
    if "private" in low:
        return "Это приватное видео, скачать его нельзя.", False
    if "unavailable" in low or "removed" in low or "deleted" in low:
        return "Видео недоступно: оно удалено или закрыто для вашего региона.", False
    if "age" in low and "restrict" in low:
        return "Видео с возрастным ограничением, скачать его не получится.", False
    if "live" in low and "stream" in low:
        return "Прямые эфиры не поддерживаются.", False
    if "unsupported url" in low:
        return "Не получается скачать с этой ссылки: она не похожа на ссылку на видео.", False
    if "ffmpeg" in low:
        return "Не получилось обработать видео. Попробуйте другое.", True
    return f"Не получилось: {text[:250]}", False


# --- резервная копия
def backup_files() -> list[Path]:
    return [p for p in (STORE, STATS_FILE, ECON_FILE, META_FILE, METRICS_FILE, CACHE_FILE, CUSTOM_FILE) if p.exists()]


def make_backup() -> io.BytesIO | None:
    files = backup_files()
    if not files:
        return None
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as z:
        for p in files:
            z.write(p, p.name)
    buf.seek(0)
    buf.name = f"backup-{datetime.now(TZ).date().isoformat()}.zip"
    return buf


async def send_backup(bot, auto: bool = False) -> bool:
    buf = make_backup()
    if buf is None:
        return False
    try:
        await bot.send_document(OWNER_ID, buf, filename=buf.name,
                                caption=("🗂 Автоматическая копия данных бота. " if auto else "🗂 Копия данных бота. ")
                                + "Храните файл: в нём друзья, монеты и рейтинг.")
        return True
    except Exception:
        log.exception("не удалось отправить копию")
        return False


async def backup_job(context: ContextTypes.DEFAULT_TYPE):
    await send_backup(context.bot, auto=True)


async def backup_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    ok = await send_backup(context.bot)
    if not ok:
        await update.effective_message.reply_text("Пока нечего сохранять: данных ещё нет.")


# --- обновление yt-dlp
def ytdlp_version() -> str:
    try:
        return yt_dlp.version.__version__
    except Exception:
        return "?"


async def update_ytdlp() -> tuple[str, str, str]:
    """Обновляет yt-dlp и подхватывает новую версию без перезапуска. Возвращает (было, стало, ошибка)."""
    global yt_dlp
    old = ytdlp_version()
    try:
        proc = await asyncio.create_subprocess_exec(
            sys.executable, "-m", "pip", "install", "-U", "--quiet", "yt-dlp",
            stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE)
        _, err = await asyncio.wait_for(proc.communicate(), 300)
        if proc.returncode != 0:
            return old, old, (err.decode(errors="ignore") or "pip завершился с ошибкой")[-300:]
        for name in [m for m in sys.modules if m == "yt_dlp" or m.startswith("yt_dlp.")]:
            del sys.modules[name]
        importlib.invalidate_caches()
        import yt_dlp as fresh
        yt_dlp = fresh
        return old, ytdlp_version(), ""
    except Exception as e:
        return old, old, str(e)[:300]


async def ytdlp_job(context: ContextTypes.DEFAULT_TYPE):
    old, new, err = await update_ytdlp()
    if err:
        await notify_owner(context.bot, f"⚠️ Не получилось обновить yt-dlp: {err}", key="ytdlp-fail", cooldown=86400)
    elif new != old:
        await notify_owner(context.bot, f"🔄 yt-dlp обновлён: {old} → {new}", key="ytdlp-ok", cooldown=0)


async def update_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg = await update.effective_message.reply_text("🔄 Обновляю yt-dlp…")
    old, new, err = await update_ytdlp()
    await msg.edit_text(f"⚠️ Не получилось: {err}" if err else
                        (f"✅ Обновлено: {old} → {new}" if new != old else f"✅ Уже последняя версия: {new}"))


# ---------- защита от перегрузки ----------
HEAVY = asyncio.Semaphore(MAX_PARALLEL)          # общая очередь тяжёлых задач
ACTIVE: set[int] = set()                         # у кого сейчас идёт задача
JOBS: dict[int, list[float]] = defaultdict(list)    # время запусков задач по пользователям
MSGS: dict[int, list[float]] = defaultdict(list)    # время сообщений по пользователям
STRANGERS: set[int] = set()                      # посторонние, которым уже ответили


def is_owner(uid: int) -> bool:
    return uid == OWNER_ID


def url_allowed(url: str, uid: int) -> bool:
    """Друзьям можно только YouTube, TikTok и Instagram (чтобы бот не ходил на чужие адреса)."""
    if is_owner(uid):
        return True
    host = (urlparse(url).hostname or "").lower()
    return any(host == d or host.endswith("." + d) for d in FRIEND_DOMAINS)


PENDING: dict[int, float] = {}                   # заявки, ждущие решения: id -> время
DENIED: dict[int, float] = {}                    # отклонённые: id -> время (повтор через сутки)
NAMES: dict[int, str] = {}                       # имена из заявок
NOTICED: dict[int, float] = {}                   # когда последний раз отвечали «заявка уже отправлена»


async def handle_stranger(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Новый человек написал боту: отправляем владельцу заявку с кнопками."""
    user, msg, now = update.effective_user, update.effective_message, time_module.time()
    uid = user.id
    for table, ttl in ((PENDING, 7 * 86400), (DENIED, 86400)):      # чистим старое
        for k in [k for k, t in table.items() if now - t > ttl]:
            table.pop(k, None)
    if uid in PENDING or uid in DENIED:
        if msg and now - NOTICED.get(uid, 0) > 600:
            NOTICED[uid] = now
            await msg.reply_text("Заявка уже отправлена, дождитесь ответа владельца." if uid in PENDING
                                 else "Владелец отклонил заявку. Повторить можно через сутки.")
        return
    if len(PENDING) >= 20 or msg is None:
        return
    name = f"{user.full_name} (@{user.username})" if user.username else user.full_name
    NAMES[uid] = name
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("✅ Принять", callback_data=f"acc:ok:{uid}"),
         InlineKeyboardButton("❌ Отклонить", callback_data=f"acc:no:{uid}")],
        [InlineKeyboardButton("🚫 Заблокировать", callback_data=f"acc:ban:{uid}")],
    ])
    try:
        inv = META["invites"].get(uid)
        await context.bot.send_message(OWNER_ID, f"🔔 Заявка на доступ к боту\nИмя: {name}\nID: {uid}"
                                       + (f"\n🤝 Пригласил(а): {NAMES.get(inv) or USERS['approved'].get(inv) or inv}"
                                          if inv else ""), reply_markup=kb)
    except Exception:
        log.exception("заявку не удалось отправить владельцу")
        await msg.reply_text("Не получилось отправить заявку, попробуйте позже.")
        return
    PENDING[uid] = now
    await msg.reply_text("Заявка отправлена владельцу бота. Я напишу, когда он ответит.")


SEEN: dict[int, dict[int, str]] = defaultdict(dict)    # кого бот видел в группах: чат -> {id: имя}


def see(chat_id: int, user):
    if user is None or getattr(user, "is_bot", False):
        return
    d = SEEN[chat_id]
    d.pop(user.id, None)
    d[user.id] = str(user.full_name or user.id)
    while len(d) > 40:
        d.pop(next(iter(d)))


def guest_pass(update: Update, context: ContextTypes.DEFAULT_TYPE) -> bool:
    """Не друзьям в личке разрешено только то, что нужно играм: /start с игровой ссылкой,
    кнопки мафии и текст анонимного вопроса."""
    q = update.callback_query
    if q is not None:
        return (q.data or "").startswith("mf:")
    msg = update.effective_message
    text = msg.text if msg is not None and isinstance(msg.text, str) else ""
    if text.startswith(("/start g", "/start ask_", "/start inv_")):
        return True
    return bool(context.user_data.get("ask")) and not text.startswith("/")


async def guard(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Срабатывает первым на любое обновление: пропускает только своих и режет флуд."""
    user = update.effective_user
    chat = update.effective_chat
    if user is None:
        raise ApplicationHandlerStop
    if update.inline_query is not None:                      # inline-запросы: решает on_inline
        if user.id in USERS["blocked"]:
            raise ApplicationHandlerStop
        return
    if chat is not None and chat.type != "private":          # группы: только одобренные владельцем
        if update.my_chat_member is None:
            if chat.id not in USERS["groups"] or user.id in USERS["blocked"]:
                raise ApplicationHandlerStop
            now = time_module.time()
            recent = [t for t in MSGS[chat.id] if now - t < 60]
            if len(recent) >= 60:                            # не больше 60 нажатий в минуту на группу
                MSGS[chat.id] = recent
                raise ApplicationHandlerStop
            recent.append(now)
            MSGS[chat.id] = recent
            see(chat.id, user)
            metric("msgs", user.id)
        return
    if not is_allowed(user.id):
        if user.id in USERS["blocked"]:
            raise ApplicationHandlerStop
        if not guest_pass(update, context):
            if not update.callback_query:
                await handle_stranger(update, context)
            raise ApplicationHandlerStop
    if not is_owner(user.id):
        now = time_module.time()
        recent = [t for t in MSGS[user.id] if now - t < 60]
        if len(recent) >= 20:                    # не больше 20 сообщений в минуту
            MSGS[user.id] = recent
            raise ApplicationHandlerStop
        recent.append(now)
        MSGS[user.id] = recent
    metric("msgs", user.id)


async def _safe_edit(msg, text: str):
    """Обновить статус-сообщение, не падая, если не получилось."""
    try:
        if msg:
            await msg.edit_text(text)
    except Exception:
        pass


async def start_job(update: Update) -> bool:
    """Друзьям: одна задача за раз и не больше FRIEND_JOBS_PER_HOUR в час."""
    uid = update.effective_user.id
    if is_owner(uid):
        return True
    msg = update.effective_message
    if uid in ACTIVE:
        await msg.reply_text("Сначала дождитесь окончания предыдущей задачи.")
        return False
    now = time_module.time()
    recent = [t for t in JOBS[uid] if now - t < 3600]
    if len(recent) >= FRIEND_JOBS_PER_HOUR:
        wait = int((recent[0] + 3600 - now) // 60) + 1
        JOBS[uid] = recent
        await msg.reply_text(f"Лимит: {FRIEND_JOBS_PER_HOUR} задач в час. Попробуйте через {wait} мин.")
        return False
    recent.append(now)
    JOBS[uid] = recent
    ACTIVE.add(uid)
    return True


def end_job(update: Update):
    ACTIVE.discard(update.effective_user.id)


def _limit_filter(info, *, incomplete=False):
    """Для друзей: не берём прямые эфиры и слишком длинные видео."""
    if info.get("is_live"):
        return "прямой эфир"
    duration = info.get("duration")
    if duration and duration > FRIEND_MAX_MIN * 60:
        return "слишком длинное видео"
    return None


# ---------- скачивание (yt-dlp) ----------
def _download(url: str, audio: bool, outdir: str, limited: bool = False) -> str:
    opts = {
        "outtmpl": f"{outdir}/%(id)s.%(ext)s",
        "noplaylist": True,
        "quiet": True,
        "socket_timeout": 30,
        "retries": 3,
    }
    if limited:
        opts["max_filesize"] = FRIEND_MAX_MB * 1024 * 1024
        opts["match_filter"] = _limit_filter
    if os.path.exists("cookies.txt"):            # нужен для части Instagram-видео
        opts["cookiefile"] = "cookies.txt"
    if audio:
        opts["format"] = "bestaudio/best"
        opts["postprocessors"] = [{
            "key": "FFmpegExtractAudio", "preferredcodec": "mp3", "preferredquality": "192",
        }]
    else:
        opts["format"] = "bv*[height<=720][vcodec^=avc1]+ba[ext=m4a]/b[height<=720][ext=mp4]/bv*[height<=720]+ba/b[height<=720]/b"
        opts["merge_output_format"] = "mp4"
    with yt_dlp.YoutubeDL(opts) as ydl:
        info = ydl.extract_info(url, download=True)
        done = (info or {}).get("requested_downloads")
        if not done:
            raise RuntimeError(
                f"Видео не скачано: оно длиннее {FRIEND_MAX_MIN} мин, больше {FRIEND_MAX_MB} МБ "
                "или это прямой эфир." if limited else "Видео не скачано.")
        return done[0]["filepath"]


async def split_file(path: str) -> list[str]:
    """Режет файл на части меньше MAX_UPLOAD без перекодирования."""
    proc = await asyncio.create_subprocess_exec(
        "ffprobe", "-v", "error", "-show_entries", "format=duration",
        "-of", "default=nw=1:nk=1", path,
        stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.DEVNULL,
    )
    out, _ = await proc.communicate()
    duration = float(out.decode().strip())
    parts = math.ceil(os.path.getsize(path) * 1.15 / MAX_UPLOAD)   # запас на неровные куски
    p = Path(path)
    pattern = str(p.with_name(f"{p.stem}_part%03d{p.suffix}"))
    await ffmpeg("-i", path, "-c", "copy", "-f", "segment",
                 "-segment_time", str(int(duration / parts) + 1),
                 "-reset_timestamps", "1", pattern)
    return sorted(str(x) for x in p.parent.glob(f"{p.stem}_part*{p.suffix}"))


# ---------- кэш скачанного ----------
CACHE = _load_json(CACHE_FILE, {})                 # ключ -> {ids: [file_id], audio: bool, t: время}
CACHE_MAX, CACHE_TTL = 500, 30 * 86400


def cache_key(url: str, audio: bool, limited: bool) -> str | None:
    p = urlparse(url)
    host = (p.hostname or "").lower().removeprefix("www.").removeprefix("m.")
    ident = None
    if host == "youtu.be":
        ident = p.path.strip("/").split("/")[0]
        host = "youtube.com"
    elif host.endswith("youtube.com"):
        ident = (parse_qs(p.query).get("v") or [None])[0]
        if not ident and p.path.startswith(("/shorts/", "/live/", "/embed/")):
            ident = p.path.split("/")[2] if len(p.path.split("/")) > 2 else None
        host = "youtube.com"
    elif host.endswith("tiktok.com") or host.endswith("instagram.com"):
        ident = p.path.strip("/")
    if not ident:
        return None
    return f"{host}:{ident}:{'a' if audio else 'v'}:{'f' if limited else 'o'}"


def cache_get(key: str | None):
    if not key:
        return None
    e = CACHE.get(key)
    if e and time_module.time() - e.get("t", 0) < CACHE_TTL and e.get("ids"):
        return e
    CACHE.pop(key, None)
    return None


def cache_put(key: str | None, ids: list, audio: bool):
    ids = [i for i in ids if isinstance(i, str)]
    if not key or not ids:
        return
    CACHE[key] = {"ids": ids, "audio": audio, "t": time_module.time()}
    while len(CACHE) > CACHE_MAX:
        CACHE.pop(min(CACHE, key=lambda k: CACHE[k]["t"]))
    _save_json(CACHE_FILE, CACHE)


async def send_cached(update: Update, ids: list, audio: bool):
    reply = update.effective_message
    for i, fid in enumerate(ids, 1):
        cap = f"Часть {i}/{len(ids)}" if len(ids) > 1 else None
        if audio:
            await reply.reply_audio(fid, caption=cap)
        else:
            await reply.reply_video(fid, caption=cap, supports_streaming=True)


# ---------- очередь с номерами ----------
WAITERS: list = []                                 # (метка, сообщение) в порядке очереди


async def _show_queue():
    for i, (_, m) in enumerate(list(WAITERS), 1):
        await _safe_edit(m, f"⏳ Вы {i}-й в очереди. Начну, как только освободится место.")


async def run_heavy(msg, work):
    """Выполняет тяжёлую задачу в общей очереди; ожидающим показывает их номер."""
    token = None
    if HEAVY.locked():
        token = object()
        WAITERS.append((token, msg))
        await _show_queue()
    try:
        async with HEAVY:
            if token is not None:
                WAITERS[:] = [w for w in WAITERS if w[0] is not token]
                token = None
                spawn(_show_queue())
            return await work()
    finally:
        if token is not None:                      # отменили, пока ждали
            WAITERS[:] = [w for w in WAITERS if w[0] is not token]


# ---------- отправка и нарезка ----------
def _fid(m, audio: bool):
    obj = getattr(m, "audio" if audio else "video", None)
    return getattr(obj, "file_id", None)


async def send_media(update: Update, path: str, audio: bool) -> list:
    files = [path]
    if os.path.getsize(path) > MAX_UPLOAD:
        await update.effective_message.reply_text("Файл большой, отправлю частями.")
        files = await split_file(path)
    ids = []
    for i, part in enumerate(files, 1):
        caption = f"Часть {i}/{len(files)}" if len(files) > 1 else None
        with open(part, "rb") as f:
            if audio:
                m = await update.effective_message.reply_audio(f, caption=caption)
            else:
                m = await update.effective_message.reply_video(f, caption=caption, supports_streaming=True,
                                                               **await video_kwargs(part))
        ids.append(_fid(m, audio))
    return ids



async def video_info(path: str) -> dict:
    """Размеры, кодек, пиксельный аспект и длительность видео (через ffprobe)."""
    proc = await asyncio.create_subprocess_exec(
        "ffprobe", "-v", "error", "-select_streams", "v:0", "-show_streams", "-show_format", "-of", "json", path,
        stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.DEVNULL)
    out, _ = await proc.communicate()
    try:
        data = json.loads(out.decode())
        st = data["streams"][0]
        w, h = int(st["width"]), int(st["height"])
        try:
            a, b = map(float, str(st.get("sample_aspect_ratio", "1:1")).split(":"))
            sar = a / b if a and b else 1.0
        except Exception:
            sar = 1.0
        rot = 0
        for sd in st.get("side_data_list", []) or []:
            rot = int(float(sd.get("rotation", 0) or 0))
        if abs(rot) in (90, 270):
            w, h = h, w
        dur = float(data.get("format", {}).get("duration") or st.get("duration") or 0)
        return {"w": w, "h": h, "sar": sar, "codec": st.get("codec_name", ""), "dur": dur, "rot": rot}
    except Exception:
        return {}


async def fix_video(path: str) -> str:
    """Если видео не H.264 или с «кривыми» пикселями, приводит к обычному виду, иначе Telegram показывает его криво."""
    info = await video_info(path)
    if not info or (info["codec"] == "h264" and abs(info["sar"] - 1) < 0.01 and not info["rot"]):
        return path
    out = str(Path(path).with_name(Path(path).stem + "_fix.mp4"))
    await ffmpeg("-i", path, "-vf", "scale=trunc(iw*sar/2)*2:trunc(ih/2)*2,setsar=1", "-c:v", "libx264",
                 "-preset", "veryfast", "-crf", "24", "-pix_fmt", "yuv420p", "-c:a", "aac", "-b:a", "128k",
                 "-movflags", "+faststart", out, timeout=3000)
    return out


async def video_kwargs(path: str) -> dict:
    info = await video_info(path)
    if not info:
        return {}
    w = max(1, round(info["w"] * info["sar"])) if info["sar"] > 1 else info["w"]
    h = info["h"]
    return {"width": w, "height": h, "duration": int(info["dur"])} if w and h else {}


async def probe_duration(path: str) -> float:
    proc = await asyncio.create_subprocess_exec(
        "ffprobe", "-v", "error", "-show_entries", "format=duration", "-of", "default=nw=1:nk=1", path,
        stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.DEVNULL)
    out, _ = await proc.communicate()
    return float(out.decode().strip())


async def shrink_to_fit(part: Path) -> Path:
    """Перекодирует кусок видео так, чтобы он поместился в лимит Telegram."""
    dur = max(1.0, await probe_duration(str(part)))
    vb = int(MAX_UPLOAD * 8 * 0.9 / dur) - 96_000
    if vb < 150_000:
        raise RuntimeError("Кусок слишком длинный для отправки, выберите меньшую длину.")
    out = part.with_name(part.stem + "_s.mp4")
    await ffmpeg("-i", str(part), "-vf", "scale=-2:720", "-c:v", "libx264", "-preset", "veryfast",
                 "-b:v", str(vb), "-maxrate", str(vb), "-bufsize", str(vb * 2), "-c:a", "aac", "-b:a", "96k", str(out))
    return out


MAX_CUT_PARTS = 30


async def cut_and_send(update: Update, msg, path: str, audio: bool, minutes: int, tmp: str):
    ext = Path(path).suffix
    pattern = str(Path(tmp) / f"cut%03d{ext}")
    await _safe_edit(msg, "✂️ Режу на части…")
    await ffmpeg("-i", path, "-c", "copy", "-f", "segment", "-segment_time", str(minutes * 60),
                 "-reset_timestamps", "1", pattern)
    parts = sorted(Path(tmp).glob(f"cut*{ext}"))
    if not parts:
        raise RuntimeError("Не получилось нарезать это видео.")
    if len(parts) > MAX_CUT_PARTS:
        raise RuntimeError(f"Получается {len(parts)} частей, это слишком много. Выберите длиннее.")
    reply = update.effective_message
    for i, part in enumerate(parts, 1):
        await _safe_edit(msg, f"📤 Отправляю часть {i} из {len(parts)}…")
        send = part
        if part.stat().st_size > MAX_UPLOAD:
            send = await shrink_to_fit(part)
        cap = f"Часть {i}/{len(parts)}"
        with open(send, "rb") as f:
            if audio:
                await reply.reply_audio(f, caption=cap)
            else:
                await reply.reply_video(f, caption=cap, supports_streaming=True, **await video_kwargs(str(send)))


async def download_and_send(update: Update, url: str, audio: bool = False, cut_min: int | None = None):
    uid = update.effective_user.id
    if not url_allowed(url, uid):
        await update.effective_message.reply_text("Поддерживаются ссылки YouTube, TikTok и Instagram.")
        return
    limited = not is_owner(uid)
    key = None if cut_min else cache_key(url, audio, limited)
    entry = cache_get(key)
    if entry:                                      # уже скачивали: отправляем сразу
        try:
            await send_cached(update, entry["ids"], audio)
            metric("cache_hits", uid)
            return
        except Exception:
            log.warning("кэш устарел, скачиваю заново")
            CACHE.pop(key, None)
    if not await start_job(update):
        return
    tmp = tempfile.mkdtemp()
    msg = None
    try:
        msg = await update.effective_message.reply_text(
            "⏳ В очереди, скоро начну…" if HEAVY.locked() else "🔎 Проверяю ссылку…")

        async def work():
            await _safe_edit(msg, "⬇️ Скачиваю…")
            path = await asyncio.to_thread(_download, url, audio, tmp, limited)
            if not audio:
                await _safe_edit(msg, "🎞 Проверяю формат…")
                path = await fix_video(path)
            if cut_min:
                await cut_and_send(update, msg, path, audio, cut_min, tmp)
            else:
                await _safe_edit(msg, "📤 Отправляю…")
                cache_put(key, await send_media(update, path, audio), audio)

        await run_heavy(msg, work)
        metric("downloads", uid)
        await msg.delete()
    except Exception as e:
        log.exception("download failed")
        metric("errors")
        text, alert = explain_error(str(e))
        if msg:
            await _safe_edit(msg, f"❌ {text}")
        if alert and APP_BOT is not None:
            await notify_owner(APP_BOT, f"⚠️ Проблема со скачиванием: {str(e)[:400]}\nСсылка: {url[:200]}",
                               key="dl:" + text[:30], cooldown=3600)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
        end_job(update)


# ---------- inline-режим ----------
PENDING_DL: dict[str, tuple[int, str, float]] = {}     # метка -> (кто, ссылка, время)


def new_dl_token(uid: int, url: str) -> str:
    now = time_module.time()
    for k in [k for k, v in PENDING_DL.items() if now - v[2] > 3600]:
        PENDING_DL.pop(k, None)
    while len(PENDING_DL) > 200:
        PENDING_DL.pop(next(iter(PENDING_DL)))
    token = secrets.token_hex(5)
    PENDING_DL[token] = (uid, url, now)
    return token


async def on_inline(update: Update, context: ContextTypes.DEFAULT_TYPE):
    iq = update.inline_query
    uid = iq.from_user.id
    if not is_allowed(uid):
        await iq.answer([], cache_time=10, button=InlineQueryResultsButton("Нужен доступ к боту", start_parameter="g"))
        return
    m = URL_RE.search(iq.query or "")
    results, button = [], None
    if m and url_allowed(m.group(0), uid):
        url = m.group(0)
        for audio in (False, True):
            e = cache_get(cache_key(url, audio, not is_owner(uid)))
            if e and len(e["ids"]) == 1:
                rid = hashlib.md5(e["ids"][0].encode()).hexdigest()[:20]
                results.append(InlineQueryResultCachedAudio(rid, e["ids"][0]) if audio
                               else InlineQueryResultCachedVideo(rid, e["ids"][0], title="🎬 Видео"))
        if not results:
            button = InlineQueryResultsButton("📥 Скачать в боте", start_parameter="dl_" + new_dl_token(uid, url))
    elif m:
        button = InlineQueryResultsButton("Поддерживаются YouTube, TikTok и Instagram", start_parameter="g")
    else:
        button = InlineQueryResultsButton("Вставьте ссылку на видео", start_parameter="g")
    await iq.answer(results, cache_time=3, is_personal=True, button=button)


async def start_download_by_token(update: Update, context: ContextTypes.DEFAULT_TYPE, token: str):
    item = PENDING_DL.pop(token, None)
    uid = update.effective_user.id
    if not item or item[0] != uid:
        await update.message.reply_text("Эта ссылка устарела. Повторите запрос в чате.")
        return
    await download_and_send(update, item[1])
    await update.message.reply_text("Готово! Теперь вернитесь в чат и снова напишите имя бота со ссылкой: "
                                    "видео появится мгновенно.")




# ---------- конвертер (ffmpeg / Pillow) ----------
async def ffmpeg(*args: str, timeout: int = 1200):
    proc = await asyncio.create_subprocess_exec(
        "ffmpeg", "-y", *args,
        stdout=asyncio.subprocess.DEVNULL, stderr=asyncio.subprocess.PIPE,
    )
    try:
        _, err = await asyncio.wait_for(proc.communicate(), timeout)
    except asyncio.TimeoutError:
        proc.kill()
        await proc.wait()
        raise RuntimeError("Обработка заняла слишком много времени и была остановлена.")
    if proc.returncode != 0:
        raise RuntimeError(err.decode()[-300:])


async def _convert_work(update: Update, tmp: Path, src: Path, mode: str):
    reply = update.effective_message
    if mode == "pdf":
        out = tmp / "result.pdf"
        Image.open(src).convert("RGB").save(out)
        await reply.reply_document(open(out, "rb"))
    elif mode == "sticker":
        img = ImageOps.exif_transpose(Image.open(src)).convert("RGBA")
        scale = 512 / max(img.size)                   # одна сторона ровно 512 px
        img = img.resize((max(1, round(img.width * scale)), max(1, round(img.height * scale))),
                         Image.LANCZOS)
        out = tmp / "sticker.webp"
        for quality in (90, 75, 60, 40):              # стикер должен быть меньше 512 КБ
            img.save(out, "WEBP", quality=quality)
            if out.stat().st_size < 500 * 1024:
                break
        await reply.reply_sticker(open(out, "rb"))
    elif mode == "qrread":
        import cv2                                    # тяжёлая библиотека, грузим только здесь
        text, _, _ = cv2.QRCodeDetector().detectAndDecode(cv2.imread(str(src)))
        await reply.reply_text(text or "QR-код на картинке не найден.")
    elif mode == "mp3":
        out = tmp / "result.mp3"
        await ffmpeg("-i", str(src), "-vn", "-acodec", "libmp3lame", "-q:a", "2", str(out))
        await reply.reply_audio(open(out, "rb"))
    elif mode == "compress":
        out = tmp / "result.mp4"
        await ffmpeg("-i", str(src), "-vf", "scale=-2:720", "-vcodec", "libx264",
                     "-crf", "28", "-preset", "veryfast", "-acodec", "aac",
                     "-b:a", "96k", str(out))
        await reply.reply_video(open(out, "rb"))


async def convert(update: Update, context: ContextTypes.DEFAULT_TYPE, mode: str):
    fid = context.user_data.get("fid")
    if not fid:
        await update.effective_message.reply_text("Сначала пришли файл.")
        return
    if not await start_job(update):
        return
    tmp = Path(tempfile.mkdtemp())
    msg = None
    try:
        msg = await update.effective_message.reply_text(
            "⏳ В очереди, скоро начну…" if HEAVY.locked() else "📥 Получаю файл…")
        tg_file = await context.bot.get_file(fid)    # лимит скачивания у бота — 20 МБ
        if not is_owner(update.effective_user.id) and (tg_file.file_size or 0) > FRIEND_MAX_MB * 1024 * 1024:
            raise RuntimeError(f"Файл больше {FRIEND_MAX_MB} МБ.")
        src = tmp / "input"

        async def work():
            await tg_file.download_to_drive(src)
            await _safe_edit(msg, "⚙️ Обрабатываю…")
            await _convert_work(update, tmp, src, mode)

        await run_heavy(msg, work)
        metric("converts", update.effective_user.id)
        await msg.delete()
    except Exception as e:
        log.exception("convert failed")
        metric("errors")
        if msg:
            await msg.edit_text(f"❌ Ошибка: {str(e)[:300]}")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
        end_job(update)


# ---------- утренняя сводка ----------
async def _geocode(c: httpx.AsyncClient, city: str | None = None) -> dict:
    geo = (await c.get("https://geocoding-api.open-meteo.com/v1/search",
                       params={"name": city or CITY, "count": 1, "language": "ru"})).json()
    if not geo.get("results"):
        raise LookupError(city or CITY)
    return geo["results"][0]


async def get_forecast(hours=(2, 4, 6), city: str | None = None) -> str:
    """Погода сейчас и через 2, 4, 6 часов."""
    async with httpx.AsyncClient(timeout=15) as c:
        place = await _geocode(c, city)
        w = (await c.get("https://api.open-meteo.com/v1/forecast", params={
            "latitude": place["latitude"], "longitude": place["longitude"],
            "current": "temperature_2m,weather_code",
            "hourly": "temperature_2m,precipitation_probability,weather_code",
            "timezone": "auto", "forecast_days": 2,
        })).json()
    cur, h = w["current"], w["hourly"]
    i = h["time"].index(cur["time"][:13] + ":00")          # индекс текущего часа
    lines = [f"🌍 {place['name']}",
             f"Сейчас: {cur['temperature_2m']:.0f} °C, {WEATHER_CODES.get(cur['weather_code'], '')}"]
    for d in hours:
        j = i + d
        rain = h["precipitation_probability"][j] or 0
        lines.append(f"Через {d} ч ({h['time'][j][11:16]}): {h['temperature_2m'][j]:.0f} °C, "
                     f"{WEATHER_CODES.get(h['weather_code'][j], '')}, осадки {rain}%")
    return "\n".join(lines)


async def get_weather(city: str | None = None) -> str:
    async with httpx.AsyncClient(timeout=15) as c:
        place = await _geocode(c, city)
        w = (await c.get("https://api.open-meteo.com/v1/forecast", params={
            "latitude": place["latitude"], "longitude": place["longitude"],
            "daily": "temperature_2m_max,temperature_2m_min,precipitation_probability_max,weathercode",
            "timezone": "auto", "forecast_days": 1,
        })).json()["daily"]
    desc = WEATHER_CODES.get(w["weathercode"][0], "")
    return (f"🌍 {place['name']}: {desc}\n"
            f"🌡 {w['temperature_2m_min'][0]:.0f}…{w['temperature_2m_max'][0]:.0f} °C, "
            f"осадки: {w['precipitation_probability_max'][0]}%")


def _fetch_news(per_feed: int = 3) -> str:
    lines = []
    for url in NEWS_FEEDS:
        for e in feedparser.parse(url).entries[:per_feed]:
            lines.append(f"• <a href=\"{e.link}\">{e.title}</a>")
    return "\n".join(lines) or "Новости сейчас недоступны."


# (утренняя карточка — ниже, в разделе «Утренняя карточка»)


# ---------- оповещение о дожде ----------
RAIN_MM = 0.1                    # осадков за 15 минут, с которых считаем, что дождь начался
RAIN_COOLDOWN = 90 * 60          # не чаще одного оповещения в полтора часа


RAIN_STATE: dict[int, dict] = defaultdict(dict)     # у каждого свои: уже оповещён, время последнего


async def check_rain(context: ContextTypes.DEFAULT_TYPE):
    """Раз в 10 минут смотрит прогноз на 15-минутных интервалах. Город запрашиваем один раз на всех."""
    groups: dict[str, list[int]] = defaultdict(list)
    for uid in subscribers("rain"):
        groups[city_of(uid)].append(uid)
    for city, uids in groups.items():
        try:
            async with httpx.AsyncClient(timeout=15) as c:
                place = await _geocode(c, city)
                w = (await c.get("https://api.open-meteo.com/v1/forecast", params={
                    "latitude": place["latitude"], "longitude": place["longitude"],
                    "current": "temperature_2m",
                    "minutely_15": "precipitation,snowfall",
                    "timezone": "auto", "forecast_days": 2,
                })).json()
            m = w["minutely_15"]
            now = w["current"]["time"]
            idx = max((i for i, t in enumerate(m["time"]) if t <= now), default=0)
            precip = [p or 0 for p in m["precipitation"]]
            snow = [x or 0 for x in m["snowfall"]]
        except Exception:
            log.exception("rain check failed: %s", city)
            continue

        window = precip[idx: idx + 9]             # текущий момент + следующие 2 часа
        if window[0] >= RAIN_MM or all(p < RAIN_MM for p in window):
            for uid in uids:                      # дождь уже идёт или не ожидается: ждём следующего
                RAIN_STATE[uid]["alerted"] = False
            continue
        soon = [k for k in (1, 2) if precip[idx + k] >= RAIN_MM]   # через 15 и 30 минут
        if not soon:
            continue
        what = "пойдёт снег ❄️" if any(snow[idx + k] > 0 for k in soon) else "пойдёт дождь ☔"
        for uid in uids:
            st = RAIN_STATE[uid]
            if st.get("alerted") or time_module.time() - st.get("last", 0) < RAIN_COOLDOWN:
                continue
            try:
                await context.bot.send_message(
                    uid, f"Примерно через {soon[0] * 15} мин {what} ({place['name']})")
                st["alerted"] = True
                st["last"] = time_module.time()
            except Exception:
                log.exception("оповещение о дожде не доставлено: %s", uid)


async def rain_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    on = not pref(uid, "rain")
    USERS["prefs"].setdefault(uid, {})["rain"] = on
    _save_users()
    await update.effective_message.reply_text(
        f"☔ Оповещения о дожде включены (город: {city_of(uid)}). Напишу за полчаса до осадков."
        if on else "Оповещения о дожде выключены.")


# ---------- QR-коды ----------
async def send_qr(update: Update, text: str):
    text = text.strip()
    if not text:
        await update.effective_message.reply_text("Пришлите текст или ссылку для QR-кода.")
        return
    if len(text) > 1000:
        await update.effective_message.reply_text("Слишком длинный текст для QR-кода (максимум 1000 символов).")
        return
    try:
        qr = qrcode.QRCode(box_size=12, border=4)
        qr.add_data(text)
        qr.make(fit=True)
        buf = io.BytesIO()
        qr.make_image(fill_color="black", back_color="white").save(buf, "PNG")
        buf.seek(0)
        await update.effective_message.reply_photo(buf)
    except Exception:
        log.exception("qr failed")
        await update.effective_message.reply_text("Не получилось сделать QR-код из этого текста.")


async def qr_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    parts = (update.message.text or "").split(maxsplit=1)
    if len(parts) < 2 or not parts[1].strip():
        await m_qr(update, context)                  # без текста: спросим, что закодировать
        return
    await send_qr(update, parts[1])





# ====================== общие помощники ======================
def _kb(*rows) -> InlineKeyboardMarkup:
    """Кнопки из списков пар (текст, callback_data) или (текст, "url", ссылка)."""
    out = []
    for row in rows:
        line = []
        for b in row:
            if len(b) == 3:
                line.append(InlineKeyboardButton(b[0], url=b[2]))
            else:
                line.append(InlineKeyboardButton(b[0], callback_data=b[1]))
        out.append(line)
    return InlineKeyboardMarkup(out)


TASKS: set = set()                                # ссылки на фоновые задачи (чтобы их не собрал сборщик мусора)


def spawn(coro):
    t = asyncio.create_task(coro)
    TASKS.add(t)
    t.add_done_callback(TASKS.discard)
    return t


async def show(q, text: str, kb=None, parse="HTML"):
    """Заменить текст сообщения с кнопками на месте (без нового сообщения)."""
    try:
        await q.edit_message_text(text, parse_mode=parse, reply_markup=kb, disable_web_page_preview=True)
    except Exception as e:
        if "not modified" not in str(e).lower():
            log.warning("не удалось обновить сообщение: %s", e)


def _name(user) -> str:
    return str(user.full_name or user.first_name or user.id)


def today():
    return datetime.now(TZ).date()


# ====================== вопросы дня ======================
# ====================== вопрос дня ======================
QOD = [
    ("У отца Мэри пять дочерей: Чача, Чече, Чичи, Чочо. Как зовут пятую?", ["Чучу", "Мэри", "Чаче", "Чиче"], 1, "Это дочь отца Мэри, то есть сама Мэри."),
    ("Что можно приготовить, но нельзя съесть?", ["Суп", "Торт", "Уроки", "Кофе"], 2, "Уроки готовят, но не едят."),
    ("Сколько месяцев в году имеют 28 дней?", ["Один", "Два", "Все двенадцать", "Шесть"], 2, "В каждом месяце есть 28-е число."),
    ("Врач прописал три таблетки: принимать каждые полчаса. На сколько хватит таблеток?", ["На полтора часа", "На час", "На три часа", "На два часа"], 1, "Первую пьёте сразу, вторую через 30 минут, третью через 60."),
    ("Что тяжелее: килограмм ваты или килограмм железа?", ["Железо", "Вата", "Одинаково", "Зависит от погоды"], 2, "И то и другое весит килограмм."),
    ("Сколько животных каждого вида Моисей взял в ковчег?", ["Двух", "Семь пар", "Ни одного", "Четырёх"], 2, "В ковчег животных брал Ной, а не Моисей."),
    ("Сколько пальцев на десяти руках?", ["Сто", "Пятьдесят", "Десять", "Двадцать"], 1, "На одной руке пять пальцев: 10 × 5 = 50."),
    ("Чем больше из неё берёшь, тем больше она становится. Что это?", ["Яма", "Гора", "Река", "Мешок"], 0, "Чем больше земли вынимаешь, тем больше яма."),
    ("Чем лучше всего размешивать чай?", ["Правой рукой", "Левой рукой", "Ложкой", "Вилкой"], 2, "Чай размешивают ложкой, а не рукой."),
    ("К тройке прибавили половину от двух, а затем умножили результат на 2. Что получилось?", ["8", "7", "10", "6"], 0, "(3 + 1) × 2 = 8."),
    ("В семье двое отцов и двое сыновей. Какое минимальное число людей в такой семье?", ["Два", "Три", "Четыре", "Пять"], 1, "Дед, отец и сын: средний человек одновременно отец и сын."),
    ("Что принадлежит вам, но другие используют это чаще, чем вы?", ["Телефон", "Имя", "Дом", "Время"], 1, "Ваше имя чаще произносят другие."),
    ("Без окон, без дверей полна горница людей. Что это?", ["Автобус", "Огурец", "Шкаф", "Улей"], 1, "Классическая загадка: внутри огурца много семечек."),
    ("Зимой и летом одним цветом. Что это?", ["Ёлка", "Берёза", "Трава", "Снег"], 0, "Ёлка не меняет цвет по сезонам."),
    ("Не лает, не кусает, а в дом не пускает. Что это?", ["Забор", "Замок", "Звонок", "Окно"], 1, "Замок не пускает в дом."),
    ("Сидит дед, во сто шуб одет. Кто его раздевает, тот слёзы проливает. Что это?", ["Лук", "Капуста", "Чеснок", "Свёкла"], 0, "Лук режут со слезами."),
    ("Висит груша, нельзя скушать. Что это?", ["Лампочка", "Фонарь", "Игрушка", "Люстра"], 0, "Лампочка похожа на грушу."),
    ("Два конца, два кольца, посередине гвоздик. Что это?", ["Очки", "Ножницы", "Пинцет", "Плоскогубцы"], 1, "Ножницы: два кольца и винт посередине."),
    ("Три курицы за три дня снесли три яйца. Сколько яиц снесут 12 куриц за 12 дней?", ["12", "36", "48", "144"], 2, "Одна курица несёт одно яйцо за три дня, значит за 12 дней четыре яйца. 12 × 4 = 48."),
    ("Пять станков делают пять деталей за пять минут. За сколько минут сто станков сделают сто деталей?", ["5 минут", "100 минут", "20 минут", "1 минуту"], 0, "Каждый станок делает деталь за 5 минут, значит сто станков сделают сто деталей за те же 5 минут."),
    ("Кувшинки удваиваются каждый день. Через 48 дней они покрыли всё озеро. Когда покрыли половину?", ["Через 24 дня", "Через 47 дней", "Через 40 дней", "Через 36 дней"], 1, "За последний день площадь удвоилась, значит за день до этого была половина."),
    ("Бита и мяч вместе стоят 110 рублей. Бита дороже мяча на 100 рублей. Сколько стоит мяч?", ["10 рублей", "5 рублей", "1 рубль", "15 рублей"], 1, "Мяч 5, бита 105, вместе 110, и разница 100."),
    ("Вы обогнали бегуна, который бежал вторым. На каком месте вы теперь?", ["На первом", "На втором", "На третьем", "Последним"], 1, "Вы заняли его место, то есть второе."),
    ("Сколько раз цифра 9 встречается в числах от 1 до 100?", ["10", "19", "20", "11"], 2, "Девятка в разряде единиц: 10 раз, в разряде десятков (90-99): ещё 10 раз."),
    ("Сколько раз можно вычесть 5 из 25?", ["Пять", "Один", "Бесконечно", "Четыре"], 1, "После первого вычитания останется уже 20, а не 25."),
    ("Часы бьют 3 раза за 3 секунды. За сколько секунд они пробьют 6 раз?", ["6", "7,5", "9", "10"], 1, "Между тремя ударами два промежутка по 1,5 секунды, между шестью ударами пять промежутков: 5 × 1,5 = 7,5."),
    ("Две кошки ловят две мышки за две минуты. Сколько кошек поймают сто мышек за сто минут?", ["2", "50", "100", "10"], 0, "Каждая кошка ловит мышь за 2 минуты, за 100 минут две кошки поймают 100 мышей."),
    ("Отец старше сына на 27 лет. Через 10 лет эта разница будет...", ["Больше", "Меньше", "Такой же", "Ровно 37 лет"], 2, "Разница в возрасте не меняется."),
    ("У фермера было 17 овец. Все, кроме 9, умерли. Сколько овец осталось?", ["8", "9", "17", "0"], 1, "«Все, кроме 9» значит, что 9 остались живыми."),
    ("30 разделили на половину и прибавили 10. Что получилось?", ["25", "70", "15", "40"], 1, "30 ÷ 0,5 = 60, плюс 10 = 70."),
    ("Продолжите ряд: 2, 4, 8, 16, …", ["24", "30", "32", "64"], 2, "Каждое число вдвое больше предыдущего."),
    ("Продолжите ряд: 1, 1, 2, 3, 5, 8, …", ["11", "12", "13", "14"], 2, "Сумма двух предыдущих: 5 + 8 = 13 (числа Фибоначчи)."),
    ("Продолжите ряд: 3, 6, 12, 24, …", ["36", "48", "30", "60"], 1, "Каждое число вдвое больше предыдущего."),
    ("Какое число лишнее: 2, 3, 5, 9, 11?", ["2", "9", "5", "11"], 1, "Остальные числа простые, а 9 делится на 3."),
    ("Какое число лишнее: 4, 9, 16, 20, 25?", ["4", "9", "20", "25"], 2, "Остальные числа являются квадратами."),
    ("Сколько рёбер у куба?", ["6", "8", "12", "16"], 2, "У куба 12 рёбер, 8 вершин и 6 граней."),
    ("Чему равна сумма углов треугольника?", ["90°", "180°", "270°", "360°"], 1, "Сумма углов любого плоского треугольника равна 180°."),
    ("Сколько секунд в сутках?", ["3 600", "14 400", "86 400", "1 440"], 2, "24 × 60 × 60 = 86 400."),
    ("Чему равна половина от трёх четвертей?", ["3/8", "2/3", "1/4", "3/2"], 0, "3/4 ÷ 2 = 3/8."),
    ("Чему равно 100 − 99 + 98 − 97 + … + 2 − 1?", ["0", "1", "50", "100"], 2, "Это 50 пар вида (100 − 99), каждая равна 1."),
    ("Кто может прыгнуть выше дома?", ["Только спортсмен", "Любой: дом сам не прыгает", "Кенгуру", "Никто"], 1, "Дом не умеет прыгать, поэтому выше него прыгнет кто угодно."),
    ("Что находится посередине Парижа?", ["Эйфелева башня", "Буква «р»", "Сена", "Лувр"], 1, "В слове «Париж» посередине стоит буква «р»."),
    ("Какой знак поставить между 2 и 3, чтобы получилось число больше 2 и меньше 3?", ["Плюс", "Минус", "Запятую", "Дробь"], 2, "2,3 больше 2 и меньше 3."),
    ("Что можно увидеть с закрытыми глазами?", ["Сон", "Звёзды", "Тень", "Ничего"], 0, "Сны мы видим именно с закрытыми глазами."),
    ("Какое слово всегда пишется неправильно?", ["«Ошибка»", "«Неправильно»", "«Всегда»", "«Слово»"], 1, "Слово «неправильно» пишется правильно именно так."),
    ("У вас спичка, а в тёмной комнате лампа, свеча и камин. Что зажжёте первым?", ["Лампу", "Свечу", "Камин", "Спичку"], 3, "Сначала нужно зажечь саму спичку."),
    ("Двое играли в шахматы 4 часа. Сколько часов играл каждый из них?", ["Два", "Четыре", "Восемь", "Один"], 1, "Играли одновременно, каждый четыре часа."),
    ("Сколько месяцев в году имеют 31 день?", ["Пять", "Шесть", "Семь", "Восемь"], 2, "Январь, март, май, июль, август, октябрь, декабрь."),
    ("Какого цвета «чёрный ящик» самолёта?", ["Чёрного", "Оранжевого", "Красного", "Белого"], 1, "Бортовые самописцы красят в оранжевый, чтобы их легче было найти."),
    ("Что нельзя съесть на завтрак?", ["Кашу", "Обед и ужин", "Яичницу", "Хлеб"], 1, "Обед и ужин ещё не наступили."),
    ("Из какого стакана ничего не выпьешь?", ["Из большого", "Из пустого", "Из пластикового", "Из чужого"], 1, "Из пустого стакана пить нечего."),
    ("Как назвать три дня подряд, не используя названий дней недели?", ["Утро, день, вечер", "Вчера, сегодня, завтра", "Раньше, потом, после", "Начало, середина, конец"], 1, "Вчера, сегодня, завтра: три дня подряд."),
    ("Что легче: тонна пуха или килограмм железа?", ["Килограмм железа", "Тонна пуха", "Одинаково", "Не знаю"], 0, "Килограмм легче тонны, независимо от материала."),
    ("На столе шесть яиц, вы взяли четыре. Сколько яиц у вас?", ["Два", "Четыре", "Шесть", "Десять"], 1, "Вы взяли четыре, значит они у вас."),
    ("В какую сторону дует дым от электропоезда, едущего на север?", ["На юг", "На север", "На запад", "Никуда: электропоезд не дымит"], 3, "У электропоезда нет дыма."),
    ("Сколько разрезов нужно, чтобы распилить бревно на 5 частей?", ["Три", "Четыре", "Пять", "Шесть"], 1, "Одним разрезом получаются две части, дальше каждый разрез добавляет одну: нужно 4."),
    ("Верёвку разрезали в трёх местах. На сколько частей она распалась?", ["На три", "На четыре", "На пять", "На две"], 1, "Три разреза дают четыре куска."),
    ("У Маши три брата, у каждого брата одна сестра. Сколько всего детей в семье?", ["Три", "Четыре", "Пять", "Шесть"], 1, "Сестра у братьев это сама Маша: она плюс три брата."),
    ("Сколько будет 7 + 7 ÷ 7 + 7 × 7 − 7?", ["49", "50", "56", "55"], 1, "7 + 1 + 49 − 7 = 50."),
    ("Что получится, если перемножить все цифры от 0 до 9?", ["Миллион", "Ноль", "Один", "362 880"], 1, "Среди множителей есть ноль."),
    ("Сумма числа и его половины равна 30. Что это за число?", ["15", "20", "10", "25"], 1, "20 + 10 = 30."),
    ("Две монеты в сумме дают 15 рублей, и одна из них не пятёрка. Какие это монеты?", ["10 и 5", "7 и 8", "12 и 3", "14 и 1"], 0, "Не пятёрка только одна, вторая как раз пятёрка."),
    ("Какой болезнью на суше никто не болеет, а в море болеют?", ["Цингой", "Морской болезнью", "Ангиной", "Гриппом"], 1, "Морской болезнью болеют именно в море."),
]


# ====================== экономика: монеты, бонусы, магазин, рейтинги ======================
ECON_FILE = DATA_DIR / "econ.json"
START_COINS = 500
ECON_DEFAULTS = {
    "gw": {}, "ach": [], "hidden": False, "w_key": "", "w_wins": 0, "w_prev": {}, "m_key": "", "m_wins": 0,
    "m_prev": {}, "gifts": 0, "invited": 0, "qd_day": "", "qd_last": "", "qd_streak": 0, "qd_ok": 0,
    "best_streak": 0, "gift_day": "", "gift_sum": 0, "custom_ok": 0, "champ": 0,
}


def _load_econ() -> dict:
    try:
        d = json.loads(ECON_FILE.read_text(encoding="utf-8"))
    except Exception:
        d = {}
    return {int(k): v for k, v in d.items()}


ECON = _load_econ()


def _save_econ():
    try:
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        tmp = ECON_FILE.with_suffix(".tmp")
        tmp.write_text(json.dumps({str(k): v for k, v in ECON.items()}, ensure_ascii=False), encoding="utf-8")
        tmp.replace(ECON_FILE)
    except Exception:
        log.exception("не удалось сохранить монеты")


def acct(uid: int, name=None) -> dict:
    a = ECON.get(uid)
    if a is None:
        a = ECON[uid] = {"name": str(name or uid), "coins": START_COINS, "streak": 0, "last_bonus": "",
                         "items": [], "title": "", "frame": "", "wins": 0}
    for k, v in ECON_DEFAULTS.items():
        if k not in a:
            a[k] = type(v)() if isinstance(v, (dict, list)) else v
    if name:
        a["name"] = str(name)
    return a


def add_coins(uid: int, n: int, name=None):
    a = acct(uid, name)
    a["coins"] = max(0, a["coins"] + n)
    _save_econ()


def spend(uid: int, n: int) -> bool:
    a = acct(uid)
    if n <= 0 or a["coins"] < n:
        return False
    a["coins"] -= n
    _save_econ()
    return True


TITLES = {"newbie": ("🌱 Новичок", 0), "gentleman": ("🎩 Джентльмен", 500), "fox": ("🦊 Хитрец", 800),
          "fire": ("🔥 Огонь", 1500), "king": ("👑 Король игр", 5000), "legend": ("💎 Легенда", 15000)}
FRAMES = {"star": ("✨ ", " ✨", 300), "heart": ("💗 ", " 💗", 400), "flame": ("🔥 ", " 🔥", 600),
          "crown": ("👑 ", "", 2000), "diamond": ("💎 ", " 💎", 4000)}


def shown(uid: int, name=None) -> str:
    """Имя игрока для показа (HTML): звание и рамка из магазина."""
    a = acct(uid, name)
    n = esc(a["name"])
    fr = FRAMES.get(a["frame"])
    if fr:
        n = fr[0] + n + fr[1]
    t = TITLES.get(a["title"])
    return f"{t[0]} {n}" if t else n


def lb_name(uid: int) -> str:
    """Имя для таблиц лидеров: можно скрыть, рядом число достижений."""
    a = acct(uid)
    if a["hidden"]:
        return "🕶 Скрытый игрок"
    return shown(uid) + (f" 🏅{len(a['ach'])}" if a["ach"] else "")


# --- периоды: неделя и месяц
def week_key(d=None) -> str:
    y, w, _ = (d or today()).isocalendar()
    return f"{y}-W{w:02d}"


def month_key(d=None) -> str:
    return (d or today()).strftime("%Y-%m")


def _roll(a: dict):
    for p, key in (("w", week_key()), ("m", month_key())):
        if a[f"{p}_key"] != key:
            if a[f"{p}_key"]:
                a[f"{p}_prev"] = {"key": a[f"{p}_key"], "wins": a[f"{p}_wins"]}
            a[f"{p}_key"], a[f"{p}_wins"] = key, 0


def period_wins(a: dict, p: str, key: str) -> int:
    if a[f"{p}_key"] == key:
        return a[f"{p}_wins"]
    prev = a[f"{p}_prev"]
    return prev.get("wins", 0) if prev.get("key") == key else 0


def reward(chat_id, uid: int, name: str, coins: int, win: bool = True, game: str = ""):
    """Награда: монеты и, если это победа, очко в рейтинги (группы, недели, месяца, категории)."""
    a = acct(uid, name)
    if win:
        if chat_id:
            add_group_win(chat_id, uid, name)
        a["wins"] += 1
        if game:
            a["gw"][game] = a["gw"].get(game, 0) + 1
        _roll(a)
        a["w_wins"] += 1
        a["m_wins"] += 1
    add_coins(uid, coins, name)
    ach_check(uid)


# --- достижения
ACH = {
    "first": ("🥉 Первая победа", "Выиграйте любую игру", lambda a: a["wins"] >= 1, 50),
    "w10": ("🥈 10 побед", "Одержите 10 побед", lambda a: a["wins"] >= 10, 150),
    "w50": ("🥇 50 побед", "Одержите 50 побед", lambda a: a["wins"] >= 50, 500),
    "mafia3": ("🕵️ Мафиози и комиссар", "3 победы в мафии", lambda a: a["gw"].get("mafia", 0) >= 3, 200),
    "quiz5": ("🧠 Эрудит", "5 побед в викторинах", lambda a: a["gw"].get("quiz", 0) >= 5, 200),
    "duel5": ("⚔️ Дуэлянт", "5 побед в дуэлях", lambda a: a["gw"].get("duel", 0) >= 5, 200),
    "rich2k": ("💰 Тысячник", "Накопите 2 000 монет", lambda a: a["coins"] >= 2000, 100),
    "rich10k": ("💎 Богач", "Накопите 10 000 монет", lambda a: a["coins"] >= 10000, 500),
    "streak7": ("🔥 Неделя подряд", "Бонус 7 дней подряд", lambda a: a["best_streak"] >= 7, 150),
    "streak30": ("🌟 Месяц подряд", "Бонус 30 дней подряд", lambda a: a["best_streak"] >= 30, 1000),
    "qd10": ("🧩 Умник", "10 верных ответов на вопрос дня", lambda a: a["qd_ok"] >= 10, 200),
    "gift": ("🎁 Щедрая душа", "Сделайте первый подарок", lambda a: a["gifts"] >= 1, 50),
    "invite": ("🤝 Душа компании", "Пригласите друга, и владелец его примет", lambda a: a["invited"] >= 1, 300),
    "idea": ("💡 Автор идей", "Ваш вопрос одобрен для игры", lambda a: a["custom_ok"] >= 1, 100),
    "champ": ("🏆 Чемпион недели", "Станьте первым в недельном рейтинге", lambda a: a["champ"] >= 1, 300),
}


def ach_check(uid: int) -> list[str]:
    a = acct(uid)
    new = []
    for key, (title, _, cond, prize) in ACH.items():
        if key not in a["ach"] and cond(a):
            a["ach"].append(key)
            a["coins"] += prize
            new.append(key)
            notify_user(uid, f"🏅 <b>Новое достижение!</b>\n{title}  ·  +{prize} 💰")
    if new:
        _save_econ()
    return new


def ach_view(uid: int) -> tuple[str, InlineKeyboardMarkup]:
    a = acct(uid)
    lines = [f"🏅 <b>Достижения</b>  ·  {len(a['ach'])}/{len(ACH)}\n{LINE}"]
    for key, (title, desc, _, prize) in ACH.items():
        lines.append(f"{'✅' if key in a['ach'] else '🔒'} {title}: <i>{desc}</i> (+{prize} 💰)")
    return "\n".join(lines), _kb([("‹ Профиль", "e:profile")])


# --- бонус и вопрос дня
def claim_bonus(uid: int, name=None) -> tuple[bool, int, int]:
    a = acct(uid, name)
    d = today().isoformat()
    if a["last_bonus"] == d:
        return False, 0, a["streak"]
    yest = (today() - timedelta(days=1)).isoformat()
    a["streak"] = a["streak"] + 1 if a["last_bonus"] == yest else 1
    a["best_streak"] = max(a["best_streak"], a["streak"])
    amount = 100 + 20 * (min(a["streak"], 10) - 1)
    a["last_bonus"] = d
    a["coins"] += amount
    _save_econ()
    ach_check(uid)
    return True, amount, a["streak"]


def qod_today():
    n = today().toordinal()
    text, opts, ok, exp = QOD[n % len(QOD)]
    pairs = list(enumerate(opts))
    random.Random(n).shuffle(pairs)                # у всех один и тот же порядок в этот день
    return text, [o for _, o in pairs], [i for i, (old, _) in enumerate(pairs) if old == ok][0], exp


def qod_view(uid: int) -> tuple[str, InlineKeyboardMarkup]:
    a = acct(uid)
    text, opts, ok, exp = qod_today()
    head = f"🧩 <b>Вопрос дня</b>  ·  серия {a['qd_streak']} дн.\n{LINE}\n{esc(text)}"
    if a["qd_day"] == today().isoformat():
        return (head + f"\n\n✅ Верный ответ: <b>{esc(opts[ok])}</b>\n<i>{esc(exp)}</i>\n\nНовый вопрос будет завтра.",
                _kb([("‹ Профиль", "e:profile")]))
    rows = [[(f"{'ABCD'[k]}. {o}", f"e:qa:{k}")] for k, o in enumerate(opts)]
    rows.append([("‹ Профиль", "e:profile")])
    return head + "\n\n<i>Попытка одна. Верный ответ даёт монеты, а серия подряд увеличивает награду.</i>", _kb(*rows)


def qod_answer(uid: int, k: int, name=None) -> tuple[bool, str]:
    a = acct(uid, name)
    d = today().isoformat()
    if a["qd_day"] == d:
        return False, "Сегодня вы уже отвечали."
    text, opts, ok, exp = qod_today()
    a["qd_day"] = d
    if k == ok:
        yest = (today() - timedelta(days=1)).isoformat()
        a["qd_streak"] = a["qd_streak"] + 1 if a["qd_last"] == yest else 1
        a["qd_last"] = d
        a["qd_ok"] += 1
        prize = 100 + 20 * (min(a["qd_streak"], 8) - 1)
        a["coins"] += prize
        _save_econ()
        ach_check(uid)
        return True, (f"🧩 <b>Верно!</b> +{prize} 💰 (серия {a['qd_streak']} дн.)\n{LINE}\n"
                      f"<b>{esc(opts[ok])}</b>\n<i>{esc(exp)}</i>")
    a["qd_streak"] = 0
    _save_econ()
    return True, (f"🧩 <b>Не угадали</b>\n{LINE}\nВерный ответ: <b>{esc(opts[ok])}</b>\n<i>{esc(exp)}</i>\n\n"
                  "Новый вопрос будет завтра.")


# --- рейтинги
LB_MODES = {
    "w": ("🏅 Победы", lambda a: a["wins"]),
    "c": ("💰 Монеты", lambda a: a["coins"]),
    "wk": ("📅 Неделя", lambda a: period_wins(a, "w", week_key())),
    "mo": ("🗓 Месяц", lambda a: period_wins(a, "m", month_key())),
    "m": ("🕵️ Мафия", lambda a: a["gw"].get("mafia", 0)),
    "q": ("🧠 Викторины", lambda a: a["gw"].get("quiz", 0)),
    "d": ("⚔️ Дуэли", lambda a: a["gw"].get("duel", 0)),
    "s": ("🔥 Серия бонусов", lambda a: a["best_streak"]),
    "k": ("🧩 Вопрос дня", lambda a: a["qd_ok"]),
}
LB_SHORT = {"w": "🏅 Победы", "c": "💰 Монеты", "wk": "📅 Неделя", "mo": "🗓 Месяц", "m": "🕵️ Мафия",
            "q": "🧠 Викторины", "d": "⚔️ Дуэли", "s": "🔥 Серии", "k": "🧩 Вопрос"}
MEDALS = ["🥇", "🥈", "🥉"]


def members(chat_id: int) -> set[int]:
    return set(SEEN.get(chat_id, {})) | set(STATS["group"].get(chat_id, {}))


def lb_text(mode: str, chat_id=None) -> str:
    title, fn = LB_MODES.get(mode, LB_MODES["w"])
    scope = members(chat_id) if chat_id else None
    rows = [(uid, fn(acct(uid))) for uid in list(ECON) if scope is None or uid in scope]
    rows = sorted([r for r in rows if r[1] > 0], key=lambda r: -r[1])[:10]
    head = f"🏆 <b>{title}</b>  ·  {'🌍 общий рейтинг' if chat_id is None else '👥 эта группа'}"
    body = "\n".join(f"{MEDALS[i] if i < 3 else f'{i + 1}.'} {lb_name(u)} — <b>{v}</b>" for i, (u, v) in enumerate(rows))
    return f"{head}\n{LINE}\n{body or 'Пока пусто. Сыграйте, и вы появитесь здесь!'}"


def lb_kb(prefix: str, mode: str, scope: str | None = None) -> InlineKeyboardMarkup:
    btns = [(("• " if k == mode else "") + LB_SHORT[k], f"{prefix}{k}") for k in LB_MODES]
    rows = [btns[i:i + 3] for i in range(0, len(btns), 3)]
    if scope:
        rows.append([("🌍 Общий рейтинг" if scope == "g" else "👥 Только группа",
                      f"gg:lb:{'a' if scope == 'g' else 'g'}:{mode}")])
        rows.append([("‹ Игры", "gg:menu")])
    else:
        rows.append([("‹ Профиль", "e:profile")])
    return _kb(*rows)


def place(uid: int, mode: str):
    fn = LB_MODES[mode][1]
    mine = fn(acct(uid))
    if mine <= 0:
        return None
    vals = [fn(a) for a in ECON.values() if fn(a) > 0]
    return 1 + sum(1 for v in vals if v > mine), len(vals)


# --- подарки
GIFT_MIN, GIFT_DAY, CHEQUE_TTL = 10, 500, 24 * 3600


def gift_check(src: int, n: int) -> str | None:
    a = acct(src)
    d = today().isoformat()
    if a["gift_day"] != d:
        a["gift_day"], a["gift_sum"] = d, 0
    if n < GIFT_MIN:
        return f"Минимальный подарок: {GIFT_MIN} 💰"
    if a["gift_sum"] + n > GIFT_DAY:
        return f"Лимит подарков в день: {GIFT_DAY} 💰 (осталось {GIFT_DAY - a['gift_sum']})"
    if a["coins"] < n:
        return f"Не хватает монет: у вас {a['coins']}"
    return None


def do_gift(src: int, dst: int, n: int, dst_name=None) -> str | None:
    if src == dst:
        return "Себе дарить не нужно 🙂"
    err = gift_check(src, n)
    if err:
        return err
    spend(src, n)
    a = acct(src)
    a["gift_sum"] += n
    a["gifts"] += 1
    add_coins(dst, n, dst_name)
    ach_check(src)
    ach_check(dst)
    _save_econ()
    return None


def cheque_create(uid: int, n: int) -> tuple[str | None, str | None]:
    if sum(1 for c in META["cheques"].values() if c["from"] == uid) >= 3:
        return None, "У вас уже три неполученных подарка. Подождите или отмените один."
    err = gift_check(uid, n)
    if err:
        return None, err
    spend(uid, n)
    acct(uid)["gift_sum"] += n
    token = secrets.token_hex(4)
    META["cheques"][token] = {"from": uid, "amount": n, "t": time_module.time()}
    _save_econ()
    _save_meta()
    return token, None


def cheque_claim(uid: int, token: str, name=None) -> str:
    c = META["cheques"].get(token)
    if not c:
        return "Этот подарок уже забрали или он не существует."
    if time_module.time() - c["t"] > CHEQUE_TTL:
        META["cheques"].pop(token, None)
        add_coins(c["from"], c["amount"])
        _save_meta()
        return "Срок подарка истёк, монеты вернулись отправителю."
    if c["from"] == uid:
        return "Это ваш собственный подарок: отправьте ссылку другу."
    META["cheques"].pop(token, None)
    add_coins(uid, c["amount"], name)
    sender = acct(c["from"])
    sender["gifts"] += 1
    _save_meta()
    ach_check(c["from"])
    ach_check(uid)
    notify_user(c["from"], f"🎁 {esc(str(name or 'Друг'))} забрал(а) ваш подарок: {c['amount']} 💰")
    return f"🎁 Вы получили <b>{c['amount']}</b> 💰 в подарок!"


def cheque_cancel(uid: int, token: str) -> bool:
    c = META["cheques"].get(token)
    if not c or c["from"] != uid:
        return False
    META["cheques"].pop(token, None)
    add_coins(uid, c["amount"])
    acct(uid)["gift_sum"] = max(0, acct(uid)["gift_sum"] - c["amount"])
    _save_meta()
    return True


def cheques_cleanup():
    now = time_module.time()
    for token, c in list(META["cheques"].items()):
        if now - c["t"] > CHEQUE_TTL:
            META["cheques"].pop(token, None)
            add_coins(c["from"], c["amount"])
            notify_user(c["from"], f"↩️ Подарок на {c['amount']} 💰 не забрали, монеты вернулись.")
    _save_meta()


def bot_link(bot_username: str, payload: str) -> str:
    return f"https://t.me/{bot_username}?start={payload}"


def share_url(link: str, text: str) -> str:
    return f"https://t.me/share/url?url={quote(link)}&text={quote(text)}"


# --- приглашения
def invite_reward(inviter: int, invited: int, invited_name: str):
    add_coins(inviter, 300)
    add_coins(invited, 200, invited_name)
    acct(inviter)["invited"] += 1
    _save_econ()
    ach_check(inviter)
    notify_user(inviter, f"🤝 {esc(invited_name)} принят(а) по вашему приглашению: +300 💰")
    notify_user(invited, "🤝 Вы пришли по приглашению: +200 💰 на ваш счёт.")


# --- профиль, магазин, настройки
def profile_view(uid: int) -> tuple[str, InlineKeyboardMarkup]:
    a = acct(uid)
    d = today().isoformat()
    places = []
    for mode, label in (("w", "по победам"), ("c", "по монетам")):
        p = place(uid, mode)
        if p:
            places.append(f"№{p[0]} из {p[1]} {label}")
    text = (f"👤 <b>{shown(uid)}</b>\n{LINE}\n"
            f"💰 Монеты: <b>{a['coins']}</b>\n"
            f"🏅 Побед: <b>{a['wins']}</b>  ·  достижений: <b>{len(a['ach'])}/{len(ACH)}</b>\n"
            + (f"📍 {' · '.join(places)}\n" if places else "")
            + f"🎁 Бонус: {'уже получен ✅' if a['last_bonus'] == d else 'можно забрать 🎁'} (серия {a['streak']} дн.)\n"
            f"🧩 Вопрос дня: {'отвечен ✅' if a['qd_day'] == d else 'ждёт вас'} (серия {a['qd_streak']} дн.)")
    return text, _kb([("🎁 Бонус", "e:bonus"), ("🧩 Вопрос дня", "e:qod")],
                     [("🛒 Магазин", "e:shop"), ("🏅 Достижения", "e:ach")],
                     [("🏆 Рейтинг", "e:lb:w"), ("🎁 Подарить", "e:gift")],
                     [("🤝 Пригласить", "e:inv"), ("⚙️ Настройки", "e:set")], [("‹ Меню", "m:home")])


def shop_view(uid: int) -> tuple[str, InlineKeyboardMarkup]:
    a = acct(uid)
    lines = [f"🛒 <b>Магазин</b>\n{LINE}\n💰 У вас: <b>{a['coins']}</b>\n"]
    rows, btns = [], []
    for kind, table, label in (("t", TITLES, "Звания"), ("f", FRAMES, "Рамки")):
        lines.append(f"<b>{label}</b>")
        for key, item in table.items():
            price = item[1] if kind == "t" else item[2]
            title = item[0] if kind == "t" else (item[0] + "имя" + item[1]).strip()
            owned = f"{kind}:{key}" in a["items"] or price == 0
            on = (a["title"] if kind == "t" else a["frame"]) == key
            mark = "✅ надето" if on else ("есть" if owned else f"{price} 💰")
            lines.append(f"• {title} — {mark}")
            btns.append((("✅ " if on else "") + title.strip()[:16] + ("" if owned else f" · {price}"),
                         f"e:buy:{kind}:{key}"))
        lines.append("")
    for i in range(0, len(btns), 2):
        rows.append(btns[i:i + 2])
    rows.append([("🧹 Снять звание и рамку", "e:unset")])
    rows.append([("‹ Профиль", "e:profile")])
    return "\n".join(lines), _kb(*rows)


def settings_view(uid: int) -> tuple[str, InlineKeyboardMarkup]:
    a = acct(uid)
    text = (f"⚙️ <b>Настройки</b>\n{LINE}\n"
            f"🏙 Город: <b>{esc(city_of(uid))}</b>\n"
            f"🕗 Время утренней карточки: <b>{mtime_of(uid)}</b> (по времени вашего города)\n"
            f"🕶 Скрыть имя в рейтингах: <b>{'да' if a['hidden'] else 'нет'}</b>")
    return text, _kb([("🏙 Сменить город", "e:setcity"), ("🕗 Время карточки", "e:time")],
                     [(("✅ " if a["hidden"] else "⬜ ") + "Скрыть имя в рейтингах", "e:hide")],
                     [("‹ Профиль", "e:profile")])


async def on_econ(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    user = q.from_user
    parts = q.data.split(":")[1:]
    action = parts[0]
    private = q.message.chat.type == "private"
    if not private and q.message.chat.id not in USERS["groups"]:
        await q.answer()
        return
    if private and not is_allowed(user.id):
        await q.answer()
        return
    acct(user.id, _name(user))
    uname = context.bot.username or ""

    async def refresh():
        if private and (q.message.text or "").startswith("👤"):
            await show(q, *profile_view(user.id))

    if action == "bonus":
        ok, amount, streak = claim_bonus(user.id, _name(user))
        await q.answer(f"🎁 +{amount} монет! Серия: {streak} дн." if ok
                       else "Сегодня бонус уже получен. Приходите завтра 🙂", show_alert=True)
        await refresh()
    elif action == "profile":
        await q.answer()
        await show(q, *profile_view(user.id))
    elif action == "qod":
        await q.answer()
        await show(q, *qod_view(user.id))
    elif action == "qa":
        k = int(parts[1]) if len(parts) > 1 and parts[1].isdigit() else -1
        ok, text = qod_answer(user.id, k, _name(user))
        await q.answer("Ответ принят" if ok else text, show_alert=not ok)
        if ok:
            await show(q, text, _kb([("‹ Профиль", "e:profile")]))
    elif action == "ach":
        await q.answer()
        await show(q, *ach_view(user.id))
    elif action == "shop":
        await q.answer()
        await show(q, *shop_view(user.id))
    elif action == "buy" and len(parts) == 3:
        kind, key = parts[1], parts[2]
        table = TITLES if kind == "t" else FRAMES if kind == "f" else None
        if table is None or key not in table:
            await q.answer()
            return
        price = table[key][1] if kind == "t" else table[key][2]
        a = acct(user.id)
        item_id = f"{kind}:{key}"
        if item_id not in a["items"] and price > 0:
            if not spend(user.id, price):
                await q.answer(f"Не хватает монет: нужно {price}", show_alert=True)
                return
            a["items"].append(item_id)
        a["title" if kind == "t" else "frame"] = key
        _save_econ()
        await q.answer("Надето ✨")
        await show(q, *shop_view(user.id))
    elif action == "unset":
        a = acct(user.id)
        a["title"], a["frame"] = "", ""
        _save_econ()
        await q.answer("Снято")
        await show(q, *shop_view(user.id))
    elif action == "lb":
        mode = parts[1] if len(parts) > 1 and parts[1] in LB_MODES else "w"
        await q.answer()
        await show(q, lb_text(mode), lb_kb("e:lb:", mode))
    elif action == "gift":
        await q.answer()
        a = acct(user.id)
        left = GIFT_DAY - (a["gift_sum"] if a["gift_day"] == today().isoformat() else 0)
        await show(q, f"🎁 <b>Подарить монеты</b>\n{LINE}\nВыберите сумму: я создам ссылку-подарок, перешлите её другу. "
                      f"Ссылка действует 24 часа, не забрали, монеты вернутся.\nЛимит: {GIFT_DAY} 💰 в день, "
                      f"сегодня осталось <b>{left}</b>.\n<i>В группе можно ответить на сообщение командой /gift 100.</i>",
                   _kb([(f"{n} 💰", f"e:gmk:{n}") for n in (50, 100, 250, 500)], [("‹ Профиль", "e:profile")]))
    elif action == "gmk":
        n = int(parts[1]) if len(parts) > 1 and parts[1].isdigit() else 0
        token, err = cheque_create(user.id, n)
        if err:
            await q.answer(err, show_alert=True)
            return
        await q.answer("Подарок создан 🎁")
        link = bot_link(uname, f"gift_{token}")
        await show(q, f"🎁 <b>Подарок на {n} 💰 готов</b>\n{LINE}\nПерешлите другу эту ссылку, первый, кто её откроет, "
                      f"получит монеты:\n{link}\n\n<i>Действует 24 часа.</i>",
                   _kb([("📤 Отправить другу", "url", share_url(link, "Держи подарок 🎁"))],
                       [("↩️ Отменить подарок", f"e:gcancel:{token}")], [("‹ Профиль", "e:profile")]))
    elif action == "gcancel":
        ok = cheque_cancel(user.id, parts[1] if len(parts) > 1 else "")
        await q.answer("Подарок отменён, монеты вернулись" if ok else "Подарок уже забрали", show_alert=not ok)
        await show(q, *profile_view(user.id))
    elif action == "inv":
        await q.answer()
        link = bot_link(uname, f"inv_{user.id}")
        a = acct(user.id)
        await show(q, f"🤝 <b>Пригласить друга</b>\n{LINE}\nПришлите другу эту ссылку:\n{link}\n\n"
                      "Когда владелец примет приглашённого, вы получите <b>300 💰</b>, а он <b>200 💰</b>.\n"
                      f"Уже приглашено: <b>{a['invited']}</b>",
                   _kb([("📤 Отправить другу", "url", share_url(link, "Заходи в бота, там много всего 🙂"))],
                       [("‹ Профиль", "e:profile")]))
    elif action == "set":
        await q.answer()
        await show(q, *settings_view(user.id))
    elif action == "hide":
        a = acct(user.id)
        a["hidden"] = not a["hidden"]
        _save_econ()
        await q.answer("Готово")
        await show(q, *settings_view(user.id))
    elif action == "setcity":
        await q.answer()
        context.user_data["await"] = "setcity"
        await show(q, "🏙 Напишите название вашего города, например: Казань", _kb([("‹ Настройки", "e:set")]))
    elif action == "time":
        await q.answer()
        times = ("0600", "0700", "0800", "0900", "1000", "1200")
        await show(q, "🕗 Во сколько присылать утреннюю карточку? Время по вашему городу.",
                   _kb([(f"{t[:2]}:{t[2:]}", f"e:mt:{t}") for t in times[:3]],
                       [(f"{t[:2]}:{t[2:]}", f"e:mt:{t}") for t in times[3:]], [("‹ Настройки", "e:set")]))
    elif action == "mt":
        t = parts[1] if len(parts) > 1 else ""
        if len(t) == 4 and t.isdigit() and int(t[:2]) < 24 and int(t[2:]) < 60:
            USERS["prefs"].setdefault(user.id, {})["mtime"] = f"{t[:2]}:{t[2:]}"
            _save_users()
        await q.answer("Время сохранено")
        await show(q, *settings_view(user.id))
    else:
        await q.answer()


# ====================== свои вопросы для «Правды или действия» ======================
CUSTOM = _load_json(CUSTOM_FILE, {"items": [], "pending": {}, "next": 1})
CUSTOM.setdefault("items", [])
CUSTOM.setdefault("pending", {})
CUSTOM.setdefault("next", 1)
CQ_LEVELS = {"lite": "😊 Лёгкий", "mid": "😏 Средний"}


def _save_custom():
    _save_json(CUSTOM_FILE, CUSTOM)


def custom_pick(kind: str, level: str):
    pool = [x["text"] for x in CUSTOM["items"] if x["kind"] == kind and x["level"] == level]
    return random.choice(pool) if pool and random.random() < 0.3 else None


async def cq_submit(update: Update, context: ContextTypes.DEFAULT_TYPE, kind: str, text: str):
    user, msg = update.effective_user, update.effective_message
    text = " ".join(text.split())[:200]
    if len(text) < 8:
        await msg.reply_text("Слишком коротко. Напишите вопрос или задание полностью.")
        return
    mine = [p for p in CUSTOM["pending"].values() if p["by"] == user.id]
    if len(mine) >= 3:
        await msg.reply_text("У вас уже три вопроса на проверке. Подождите решения владельца.")
        return
    cid = str(CUSTOM["next"])
    CUSTOM["next"] += 1
    CUSTOM["pending"][cid] = {"kind": kind, "text": text, "by": user.id, "name": _name(user)}
    _save_custom()
    head = "🗣 Правда" if kind == "truth" else "🎬 Действие"
    try:
        await context.bot.send_message(
            OWNER_ID, f"💡 Новый вопрос от {_name(user)} (ID {user.id})\n{head}: {text}",
            reply_markup=_kb([("✅ Лёгкий", f"cq:ok:{cid}:lite"), ("✅ Средний", f"cq:ok:{cid}:mid")],
                             [("❌ Отклонить", f"cq:no:{cid}")]))
    except Exception:
        log.exception("не удалось отправить вопрос владельцу")
    await msg.reply_text("✅ Отправил владельцу на проверку. Если одобрит, вопрос появится в игре, а вам +100 💰.",
                         reply_markup=_kb([("‹ Меню", "m:home")]))


async def on_cq(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    if not is_owner(q.from_user.id):
        return
    parts = q.data.split(":")
    action, cid = parts[1], parts[2]
    item = CUSTOM["pending"].pop(cid, None)
    if item is None:
        await q.edit_message_text("Этот вопрос уже обработан.")
        return
    if action == "ok" and len(parts) > 3 and parts[3] in CQ_LEVELS:
        CUSTOM["items"].append({"kind": item["kind"], "level": parts[3], "text": item["text"], "by": item["by"]})
        a = acct(item["by"])
        a["custom_ok"] += 1
        add_coins(item["by"], 100)
        ach_check(item["by"])
        notify_user(item["by"], "💡 Ваш вопрос одобрен и добавлен в игру: +100 💰")
        await q.edit_message_text(f"✅ Добавлен ({CQ_LEVELS[parts[3]]}): {item['text']}")
    else:
        notify_user(item["by"], "💡 Владелец не добавил ваш вопрос. Попробуйте придумать другой.")
        await q.edit_message_text(f"❌ Отклонён: {item['text']}")
    _save_custom()


# ====================== город и время утренней карточки ======================
def _prefs(uid: int) -> dict:
    return USERS["prefs"].get(uid, {})


def city_of(uid: int) -> str:
    return _prefs(uid).get("city") or (CITY if uid == OWNER_ID else FRIEND_CITY)


def tz_of(uid: int):
    name = _prefs(uid).get("tz")
    if name:
        try:
            return ZoneInfo(name)
        except Exception:
            pass
    return TZ


def mtime_of(uid: int) -> str:
    t = _prefs(uid).get("mtime") or MORNING_TIME
    try:
        h, m = map(int, t.split(":"))
        assert 0 <= h < 24 and 0 <= m < 60
        return f"{h:02d}:{m:02d}"
    except Exception:
        return "08:00"


async def set_city(uid: int, text: str) -> str | None:
    """Запоминает город пользователя (для погоды, дождя и карточки). Возвращает название или None."""
    try:
        async with httpx.AsyncClient(timeout=15) as c:
            place = await _geocode(c, text[:60])
    except Exception:
        return None
    p = USERS["prefs"].setdefault(uid, {})
    p["city"] = place["name"]
    if place.get("timezone"):
        p["tz"] = place["timezone"]
    p.pop("msent", None)
    _save_users()
    return place["name"]


async def morning_tick(context: ContextTypes.DEFAULT_TYPE):
    """Каждые 5 минут: кому пришло время карточки (по его городу и часам), тому отправляем."""
    news, cache = None, {}
    for uid in subscribers("morning"):
        pr = _prefs(uid)
        now = datetime.now(tz_of(uid))
        hh, mm = map(int, mtime_of(uid).split(":"))
        due = now.replace(hour=hh, minute=mm, second=0, microsecond=0)
        day = now.date().isoformat()
        if not (due <= now < due + timedelta(hours=3)) or pr.get("msent") == day:
            continue
        USERS["prefs"].setdefault(uid, {})["msent"] = day
        _save_users()
        if news is None:
            news = await asyncio.to_thread(_fetch_news)
        key = (city_of(uid), str(tz_of(uid)))
        if key not in cache:
            cache[key] = await morning_text(key[0], news, tz_of(uid))
        try:
            await context.bot.send_message(uid, cache[key], parse_mode="HTML", disable_web_page_preview=True,
                                           reply_markup=morning_kb(uid))
            metric("morning")
        except Exception:
            log.exception("утренняя карточка не доставлена: %s", uid)
        await asyncio.sleep(0.1)


# ====================== панель владельца и рассылка ======================
def panel_text() -> str:
    days = sorted(METRICS["days"])
    t = METRICS["days"].get(today().isoformat(), {})
    week = {}
    for d in days[-7:]:
        for k, v in METRICS["days"][d].items():
            if k != "users":
                week[k] = week.get(k, 0) + v
    wk_users = set()
    for d in days[-7:]:
        wk_users |= set(METRICS["days"][d].get("users", []))
    friends = len(USERS["approved"]) + len(ENV_ALLOWED - set(USERS["approved"]))
    up = int((time_module.time() - START_TIME) // 3600)
    coins = sum(a["coins"] for a in ECON.values())
    return (f"📊 <b>Панель владельца</b>\n{LINE}\n"
            f"👥 Друзей: <b>{friends}</b>  ·  групп: <b>{len(USERS['groups'])}</b>  ·  ожидают: <b>{len(PENDING)}</b>\n"
            f"💡 Вопросов на проверке: <b>{len(CUSTOM['pending'])}</b>\n\n"
            f"<b>Сегодня</b>\n"
            f"👤 активных: {len(t.get('users', []))}  ·  📥 скачиваний: {t.get('downloads', 0)}  ·  "
            f"⚡ из кэша: {t.get('cache_hits', 0)}\n"
            f"🔄 конвертаций: {t.get('converts', 0)}  ·  ☀️ карточек: {t.get('morning', 0)}  ·  "
            f"⚠️ ошибок: {t.get('errors', 0)}\n\n"
            f"<b>За 7 дней</b>\n"
            f"👤 активных: {len(wk_users)}  ·  📥 {week.get('downloads', 0)}  ·  ⚡ {week.get('cache_hits', 0)}  ·  "
            f"⚠️ {week.get('errors', 0)}\n\n"
            f"🗄 В кэше видео: {len(CACHE)}  ·  💰 монет в игре: {coins}\n"
            f"🔧 yt-dlp {ytdlp_version()}  ·  работаю {up} ч")


def panel_kb() -> InlineKeyboardMarkup:
    return _kb([("📣 Рассылка", "p:bc"), ("🗂 Копия данных", "p:backup")],
               [("🔄 Обновить yt-dlp", "p:upd"), ("🔃 Обновить панель", "p:home")], [("‹ Меню", "m:home")])


async def on_panel(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if not is_owner(q.from_user.id) or q.message.chat.type != "private":
        await q.answer()
        return
    act = q.data.split(":")[1]
    ud = context.user_data
    if act == "home":
        await q.answer()
        ud.pop("await", None)
        await show(q, panel_text(), panel_kb())
    elif act == "backup":
        await q.answer("Отправляю копию…")
        if not await send_backup(context.bot):
            await q.message.reply_text("Пока нечего сохранять.")
    elif act == "upd":
        await q.answer("Обновляю…")
        old, new, err = await update_ytdlp()
        await q.message.reply_text(f"⚠️ Не получилось: {err}" if err else
                                   (f"✅ yt-dlp: {old} → {new}" if new != old else f"✅ Уже последняя версия: {new}"))
    elif act == "bc":
        await q.answer()
        ud["await"] = "bc"
        await show(q, "📣 <b>Рассылка</b>\nНапишите текст: я покажу, как он выглядит, и спрошу подтверждение. "
                      "Получат все друзья.", _kb([("‹ Панель", "p:home")]))
    elif act == "bcgo":
        text = ud.pop("bc_text", None)
        if not text:
            await q.answer("Текст устарел", show_alert=True)
            return
        await q.answer("Отправляю…")
        ids = sorted(({OWNER_ID} | ENV_ALLOWED | set(USERS["approved"])) - USERS["blocked"].keys())
        spawn(_broadcast(context.bot, ids, text, q.message))
    elif act == "bcno":
        ud.pop("bc_text", None)
        await q.answer("Отменено")
        await show(q, panel_text(), panel_kb())
    else:
        await q.answer()


async def _broadcast(bot, ids: list[int], text: str, status_msg):
    ok = fail = 0
    for uid in ids:
        try:
            await bot.send_message(uid, "📣 " + text, disable_web_page_preview=True)
            ok += 1
        except Exception:
            fail += 1
        await asyncio.sleep(0.1)
    await _safe_edit(status_msg, f"📣 Рассылка завершена: доставлено {ok}, не доставлено {fail}.")


async def panel_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(panel_text(), parse_mode="HTML", reply_markup=panel_kb())


# ====================== дуэли на двоих в личке ======================
DUELS: dict[str, dict] = {}
DUEL_TTL = 3600
D_RPS = {"r": "🪨", "s": "✂️", "p": "📄"}


def du_new(uid: int, name: str, kind: str, stake: int) -> str:
    now = time_module.time()
    for k in [k for k, v in DUELS.items() if now - v["t"] > DUEL_TTL]:
        DUELS.pop(k, None)
    did = secrets.token_hex(3)
    DUELS[did] = {"t": now, "kind": kind, "stake": stake, "host": uid, "names": {uid: name}, "guest": None,
                  "state": "wait", "picks": {}, "qs": [], "i": -1, "scores": {uid: 0}, "answers": {}, "msgs": {}}
    return did


def du_menu_view(uid: int) -> tuple[str, InlineKeyboardMarkup]:
    return (f"⚔️ <b>Дуэль с другом</b>\n{LINE}\nВыберите игру. Я создам ссылку: другу достаточно её открыть "
            "(он должен быть в числе друзей бота).", _kb([("✂️ Камень-ножницы-бумага", "d:new:rps")],
                                                         [("🧠 Дуэль эрудитов", "d:new:quiz")], [("‹ Меню", "m:home")]))


async def du_send(bot, did: str, text: str, kb_fn=None):
    """Обновляет сообщение каждого игрока (или присылает новое)."""
    d = DUELS.get(did)
    if not d:
        return
    for uid in [d["host"], d["guest"]]:
        if uid is None:
            continue
        kb = kb_fn(uid) if kb_fn else None
        old = d["msgs"].get(uid)
        try:
            if old:
                await bot.edit_message_text(text, chat_id=uid, message_id=old, parse_mode="HTML", reply_markup=kb)
            else:
                m = await bot.send_message(uid, text, parse_mode="HTML", reply_markup=kb)
                d["msgs"][uid] = m.message_id
        except Exception as e:
            if "not modified" not in str(e).lower():
                try:
                    m = await bot.send_message(uid, text, parse_mode="HTML", reply_markup=kb)
                    d["msgs"][uid] = m.message_id
                except Exception:
                    log.warning("дуэль: не удалось написать игроку %s", uid)


def du_other(d: dict, uid: int) -> int:
    return d["guest"] if uid == d["host"] else d["host"]


async def du_join(update: Update, context: ContextTypes.DEFAULT_TYPE, did: str):
    user, msg = update.effective_user, update.effective_message
    d = DUELS.get(did)
    if not d or d["state"] != "wait":
        await msg.reply_text("Эта дуэль уже началась или устарела.")
        return
    if user.id == d["host"]:
        await msg.reply_text("Это ваша дуэль: отправьте ссылку другу.")
        return
    st = d["stake"]
    if st and (acct(user.id)["coins"] < st or acct(d["host"])["coins"] < st):
        await msg.reply_text(f"Для этой дуэли нужно {st} 💰 у каждого игрока.")
        return
    if st:
        spend(user.id, st)
        spend(d["host"], st)
    d["guest"] = user.id
    d["names"][user.id] = _name(user)
    d["scores"][user.id] = 0
    d["state"] = "play"
    d["msgs"] = {}
    if d["kind"] == "rps":
        await du_rps_round(context.bot, did)
    else:
        d["qs"] = [prep_q(x) for x in random.sample(QUIZ, 3)]
        spawn(du_quiz_next(context.bot, did))


def du_title(d: dict) -> str:
    h, g = d["host"], d["guest"]
    stake = f"  ·  банк {d['stake'] * 2} 💰" if d["stake"] else ""
    return (f"⚔️ <b>{'Камень-ножницы-бумага' if d['kind'] == 'rps' else 'Дуэль эрудитов'}</b>{stake}\n{LINE}\n"
            f"{esc(d['names'][h])} против {esc(d['names'][g])}\n")


async def du_rps_round(bot, did: str):
    d = DUELS[did]
    d["picks"] = {}
    kb = lambda uid: _kb([("🪨 Камень", f"d:p:{did}:r"), ("✂️ Ножницы", f"d:p:{did}:s"), ("📄 Бумага", f"d:p:{did}:p")])
    await du_send(bot, did, du_title(d) + "\nСделайте выбор: соперник не увидит его, пока вы оба не выберете.", kb)


async def du_finish(bot, did: str, winner: int | None, detail: str):
    d = DUELS.pop(did, None)
    if not d:
        return
    h, g = d["host"], d["guest"]
    pot = d["stake"] * 2
    if winner is None:
        if d["stake"]:
            add_coins(h, d["stake"])
            add_coins(g, d["stake"])
        verdict = "🤝 Ничья" + (", ставки возвращены." if d["stake"] else ".")
    else:
        loser = du_other(d, winner)
        reward(None, winner, d["names"][winner], pot + 30, game="duel")
        add_coins(loser, 20, d["names"][loser])
        verdict = f"🏆 Победил(а) <b>{shown(winner, d['names'][winner])}</b>: +{pot + 30} 💰"
    d["msgs"] = d.get("msgs", {})
    text = du_title(d) + f"\n{detail}\n\n{verdict}"
    for uid in (h, g):
        try:
            if d["msgs"].get(uid):
                await bot.edit_message_text(text, chat_id=uid, message_id=d["msgs"][uid], parse_mode="HTML",
                                            reply_markup=_kb([("⚔️ Ещё дуэль", "d:menu"), ("‹ Меню", "m:home")]))
            else:
                await bot.send_message(uid, text, parse_mode="HTML",
                                       reply_markup=_kb([("⚔️ Ещё дуэль", "d:menu"), ("‹ Меню", "m:home")]))
        except Exception:
            log.warning("дуэль: итог не доставлен %s", uid)


QUIZ_DUEL_SECONDS = 25


async def du_quiz_next(bot, did: str):
    d = DUELS.get(did)
    if not d:
        return
    d["i"] += 1
    if d["i"] >= len(d["qs"]):
        h, g = d["host"], d["guest"]
        s1, s2 = d["scores"][h], d["scores"][g]
        winner = h if s1 > s2 else g if s2 > s1 else None
        await du_finish(bot, did, winner, f"Счёт: {esc(d['names'][h])} {s1} : {s2} {esc(d['names'][g])}")
        return
    d["answers"] = {}
    i = d["i"]
    text, opts, ok = d["qs"][i][:3]
    kb = lambda uid: _kb(*[[(f"{'ABCD'[k]}. {o}", f"d:a:{did}:{i}:{k}")] for k, o in enumerate(opts)])
    await du_send(bot, did, du_title(d) + f"\n<b>Вопрос {i + 1}/{len(d['qs'])}</b>\n{esc(text)}", kb)
    spawn(du_quiz_timer(bot, did, i))


async def du_quiz_timer(bot, did: str, i: int):
    await asyncio.sleep(QUIZ_DUEL_SECONDS)
    d = DUELS.get(did)
    if d and d["i"] == i and len(d["answers"]) < 2:
        await du_quiz_reveal(bot, did, i)


async def du_quiz_reveal(bot, did: str, i: int):
    d = DUELS.get(did)
    if not d or d["i"] != i or d.get("revealing") == i:
        return
    d["revealing"] = i
    text, opts, ok = d["qs"][i][:3]
    lines = []
    for uid in (d["host"], d["guest"]):
        a = d["answers"].get(uid)
        if a == ok:
            d["scores"][uid] += 1
        lines.append(f"{esc(d['names'][uid])}: " + ("—" if a is None else ("✅" if a == ok else "❌")))
    await du_send(bot, did, du_title(d) + f"\n<b>Вопрос {i + 1}</b>: {esc(text)}\nОтвет: <b>{esc(opts[ok])}</b>\n"
                  + "\n".join(lines))
    await asyncio.sleep(3)
    await du_quiz_next(bot, did)


async def on_duel(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    user = q.from_user
    if q.message.chat.type != "private" or not is_allowed(user.id):
        await q.answer()
        return
    parts = q.data.split(":")[1:]
    act = parts[0]
    uname = context.bot.username or ""
    if act == "menu":
        await q.answer()
        await show(q, *du_menu_view(user.id))
    elif act == "new":
        kind = parts[1] if len(parts) > 1 and parts[1] in ("rps", "quiz") else "rps"
        await q.answer()
        await show(q, "Выберите ставку (её платит каждый игрок):",
                   _kb([(f"{s} 💰" if s else "Без ставки", f"d:st:{kind}:{s}") for s in (0, 50, 100)],
                       [("‹ Назад", "d:menu")]))
    elif act == "st" and len(parts) == 3:
        kind, stake = parts[1], int(parts[2]) if parts[2].isdigit() else 0
        if kind not in ("rps", "quiz") or stake not in (0, 50, 100):
            await q.answer()
            return
        if acct(user.id)["coins"] < stake:
            await q.answer(f"Не хватает монет: у вас {acct(user.id)['coins']}", show_alert=True)
            return
        did = du_new(user.id, _name(user), kind, stake)
        DUELS[did]["msgs"][user.id] = q.message.message_id
        link = bot_link(uname, f"du_{did}")
        await q.answer()
        await show(q, f"⚔️ <b>Дуэль создана</b>\n{LINE}\nПерешлите другу ссылку, и игра начнётся, как только он её откроет:\n"
                      f"{link}\n\n<i>Ссылка действует час.</i>",
                   _kb([("📤 Отправить другу", "url", share_url(link, "Давай сыграем дуэль ⚔️"))],
                       [("✖ Отменить", f"d:x:{did}")]))
    elif act == "x" and len(parts) == 2:
        d = DUELS.get(parts[1])
        if d and d["host"] == user.id and d["state"] == "wait":
            DUELS.pop(parts[1], None)
        await q.answer("Дуэль отменена")
        await show(q, *du_menu_view(user.id))
    elif act == "p" and len(parts) == 3:
        did, pick = parts[1], parts[2]
        d = DUELS.get(did)
        if not d or d["state"] != "play" or d["kind"] != "rps" or user.id not in (d["host"], d["guest"]) \
                or pick not in D_RPS:
            await q.answer("Дуэль уже закончилась", show_alert=True)
            return
        if user.id in d["picks"]:
            await q.answer("Вы уже выбрали")
            return
        d["picks"][user.id] = pick
        await q.answer("Выбор принят")
        if len(d["picks"]) < 2:
            try:
                await q.edit_message_text(du_title(d) + f"\nВы выбрали {D_RPS[pick]}. Ждём соперника…",
                                          parse_mode="HTML")
            except Exception:
                pass
            return
        h, g = d["host"], d["guest"]
        ph, pg = d["picks"][h], d["picks"][g]
        detail = f"{esc(d['names'][h])}: {D_RPS[ph]}   {esc(d['names'][g])}: {D_RPS[pg]}"
        if ph == pg:
            await du_send(context.bot, did, du_title(d) + f"\n{detail}\n\n🤝 Ничья! Играем ещё раз…")
            await asyncio.sleep(2)
            if did in DUELS:
                await du_rps_round(context.bot, did)
            return
        await du_finish(context.bot, did, h if RPS_BEATS[ph] == pg else g, detail)
    elif act == "a" and len(parts) == 4:
        did = parts[1]
        d = DUELS.get(did)
        if not d or d["state"] != "play" or d["kind"] != "quiz" or user.id not in (d["host"], d["guest"]) \
                or not parts[2].isdigit() or int(parts[2]) != d["i"] or not parts[3].isdigit():
            await q.answer("Вопрос уже закрыт")
            return
        if user.id in d["answers"]:
            await q.answer("Вы уже ответили")
            return
        d["answers"][user.id] = int(parts[3])
        await q.answer("Ответ принят")
        if len(d["answers"]) >= 2:
            spawn(du_quiz_reveal(context.bot, did, d["i"]))
    else:
        await q.answer()


# ====================== подарки в группе, подарочные ссылки, приглашения ======================
async def gift_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg, user = update.effective_message, update.effective_user
    target = msg.reply_to_message.from_user if msg.reply_to_message else None
    n = int(context.args[0]) if context.args and context.args[0].isdigit() else 0
    if target is None or target.is_bot or not n:
        await msg.reply_text("Ответьте на сообщение друга командой /gift и суммой, например: /gift 100")
        return
    acct(user.id, _name(user))
    err = do_gift(user.id, target.id, n, _name(target))
    if err:
        await msg.reply_text(err)
        return
    await msg.reply_text(f"🎁 {shown(user.id)} подарил(а) <b>{n}</b> 💰 игроку {shown(target.id, _name(target))}",
                         parse_mode="HTML")


async def on_invite_start(update: Update, context: ContextTypes.DEFAULT_TYPE, inviter_raw: str):
    """Человек пришёл по приглашению: запоминаем, кто пригласил, и отправляем заявку владельцу."""
    user = update.effective_user
    if inviter_raw.isdigit() and int(inviter_raw) != user.id and is_allowed(int(inviter_raw)) \
            and user.id not in META["invites"]:
        META["invites"][user.id] = int(inviter_raw)
        _save_meta()
    if is_allowed(user.id):
        await update.message.reply_text("Вы уже в числе друзей бота 🙂", reply_markup=reply_kb())
        return
    await update.message.reply_text("👋 Вас пригласил друг! Отправляю заявку владельцу бота…")
    await handle_stranger(update, context)


def invite_on_approve(uid: int, name: str):
    inviter = META["invites"].pop(uid, None)
    if inviter and is_allowed(inviter):
        _save_meta()
        invite_reward(inviter, uid, name)


# ====================== призы за неделю и месяц ======================
async def period_job(context: ContextTypes.DEFAULT_TYPE):
    cheques_cleanup()
    t = today()
    for p, cur_key, last, prev_key, prizes, label in (
            ("w", week_key(t), "last_week", week_key(t - timedelta(days=7)), (500, 300, 150), "недели"),
            ("m", month_key(t), "last_month", month_key((t.replace(day=1) - timedelta(days=1))),
             (2000, 1000, 500), "месяца")):
        if META[last] == cur_key:
            continue
        had = bool(META[last])
        META[last] = cur_key
        _save_meta()
        if not had:
            continue
        rows = sorted(((u, period_wins(a, p, prev_key)) for u, a in ECON.items()), key=lambda r: -r[1])
        rows = [r for r in rows if r[1] > 0][:3]
        if not rows:
            continue
        lines = []
        for i, (u, w) in enumerate(rows):
            add_coins(u, prizes[i])
            if p == "w" and i == 0:
                acct(u)["champ"] += 1
                _save_econ()
            ach_check(u)
            notify_user(u, f"🏆 Итоги {label}: вы на {i + 1}-м месте ({w} побед). Приз: +{prizes[i]} 💰")
            lines.append(f"{MEDALS[i]} {lb_name(u)}: {w} (+{prizes[i]} 💰)")
        text = f"🏆 <b>Итоги {label}</b>\n{LINE}\n" + "\n".join(lines)
        for gid in list(USERS["groups"]):
            try:
                await context.bot.send_message(gid, text, parse_mode="HTML")
            except Exception:
                pass
        await notify_owner(context.bot, "🏆 Итоги " + label + ":\n" + re.sub(r"<[^>]+>", "", "\n".join(lines)),
                           key="period-" + p, cooldown=0)


# ====================== утренняя карточка ======================
WEEKDAYS = ["Понедельник", "Вторник", "Среда", "Четверг", "Пятница", "Суббота", "Воскресенье"]
MONTHS = ["января", "февраля", "марта", "апреля", "мая", "июня", "июля", "августа", "сентября", "октября",
          "ноября", "декабря"]
FIXED_HOLIDAYS = {
    (1, 1): "Новый год", (1, 7): "Рождество Христово", (1, 25): "Татьянин день", (2, 14): "День святого Валентина",
    (2, 23): "День защитника Отечества", (3, 8): "Международный женский день", (4, 1): "День смеха",
    (4, 12): "День космонавтики", (5, 1): "Праздник Весны и Труда", (5, 9): "День Победы",
    (6, 1): "День защиты детей", (6, 12): "День России", (9, 1): "День знаний", (10, 5): "День учителя",
    (10, 31): "Хэллоуин", (11, 4): "День народного единства", (11, 14): "Всемирный день борьбы с диабетом",
    (12, 12): "День Конституции", (12, 31): "Канун Нового года",
}
FACTS = [
    "Мёд практически не портится: археологи находили съедобный мёд в гробницах Древнего Египта.",
    "У осьминога три сердца.",
    "С точки зрения ботаники банан — ягода, а клубника — нет.",
    "На Венере сутки длиннее года: она делает оборот вокруг оси за 243 земных дня, а вокруг Солнца за 225.",
    "Летом Эйфелева башня становится выше на несколько сантиметров: металл расширяется от тепла.",
    "Акулы появились раньше деревьев.",
    "Молния нагревает воздух примерно до 30 000 °C, это в несколько раз горячее поверхности Солнца.",
    "В Антарктиде хранится около 70% мировых запасов пресной воды.",
    "Сердце у креветки находится в голове.",
    "Самая короткая война в истории, англо-занзибарская 1896 года, длилась около 40 минут.",
    "Коалы спят до 20 часов в сутки.",
    "Клеопатра жила ближе по времени к высадке на Луну, чем к постройке Великой пирамиды.",
    "Улитка может спать до трёх лет подряд.",
    "Бабочки чувствуют вкус лапками.",
    "У жирафа и человека одинаковое число шейных позвонков: по семь.",
    "Первый в мире сайт появился в 1991 году.",
    "Первое электронное письмо отправил Рэй Томлинсон в 1971 году, он же выбрал знак @ для адресов.",
    "В космосе нет звука: в вакууме звуковые волны не распространяются.",
    "Свет от Солнца добирается до Земли примерно за 8 минут.",
    "Самое глубокое место океана, впадина Челленджер, находится почти на 11 километров ниже уровня моря.",
    "Печатный станок Гутенберга появился около 1450 года.",
    "Некоторые пингвины дарят партнёру камешки в знак симпатии.",
    "У страуса глаз больше, чем мозг.",
    "Радуга на самом деле круг, а с земли мы видим только его дугу.",
    "Человеческое тело каждую секунду производит около двух миллионов новых красных кровяных клеток.",
    "Сова не может вращать глазами, зато умеет поворачивать голову почти на 270 градусов.",
    "Вода в океане солёная, потому что реки веками приносят в него растворённые соли.",
    "Лимон содержит больше сахара, чем клубника, просто кислота скрывает сладость.",
    "Рекорд по продолжительности полёта курицы — 13 секунд.",
    "Мозг человека потребляет примерно пятую часть всей энергии организма.",
    "Зебры чёрные с белыми полосками или белые с чёрными, учёные до сих пор спорят, но рисунок у каждой уникален.",
    "Морская звезда не имеет мозга и крови: её тело работает на морской воде.",
    "Шахматных партий из 40 ходов больше, чем атомов во Вселенной, если верить оценкам математиков.",
]
PROVERBS = [
    "Дорогу осилит идущий.", "Не боги горшки обжигают.", "Утро вечера мудренее.", "Без труда не вынешь и рыбку из пруда.",
    "Тише едешь, дальше будешь.", "Семь раз отмерь, один раз отрежь.", "Глаза боятся, а руки делают.",
    "Что посеешь, то и пожнёшь.", "Лиха беда начало.", "Делу время, потехе час.", "Терпение и труд всё перетрут.",
    "Одна голова хорошо, а две лучше.", "Мал золотник, да дорог.", "Скажи мне, кто твой друг, и я скажу, кто ты.",
]
DAYINFO: dict[str, dict] = {}


async def day_info(d: datetime) -> dict:
    """Праздник и событие «в этот день» из русской Википедии; если не вышло, запасной список."""
    key = d.strftime("%m-%d")
    if key in DAYINFO:
        return DAYINFO[key]
    info = {"holiday": FIXED_HOLIDAYS.get((d.month, d.day)), "event": None}
    try:
        async with httpx.AsyncClient(timeout=8, headers={"User-Agent": "friends-bot/1.0"}) as c:
            r = await c.get(f"https://ru.wikipedia.org/api/rest_v1/feed/onthisday/all/{d.month:02d}/{d.day:02d}")
            data = r.json()
        hol = [h.get("text") for h in data.get("holidays", []) if h.get("text")]
        if hol and not info["holiday"]:
            info["holiday"] = hol[0].split("\n")[0][:120]
        events = [e for e in (data.get("selected") or data.get("events") or []) if e.get("text") and e.get("year")]
        if events:
            e = random.Random(key).choice(events)
            info["event"] = f"{e['year']}: {str(e['text'])[:220]}"
    except Exception:
        log.warning("праздники и события: источник недоступен, использую запасной список")
    DAYINFO[key] = info
    if len(DAYINFO) > 5:
        DAYINFO.pop(next(iter(DAYINFO)))
    return info


async def rates_line() -> str:
    try:
        async with httpx.AsyncClient(timeout=8) as c:
            v = (await c.get("https://www.cbr-xml-daily.ru/daily_json.js")).json()["Valute"]
        return f"💱 $ {v['USD']['Value']:.2f} · € {v['EUR']['Value']:.2f}"
    except Exception:
        return ""


async def morning_text(city: str | None = None, news: str | None = None, tz=None) -> str:
    d = datetime.now(tz or TZ)
    try:
        weather = await get_weather(city)
    except Exception:
        weather = "Погоду получить не удалось."
    if news is None:
        news = await asyncio.to_thread(_fetch_news)
    info = await day_info(d)
    rates = await rates_line()
    n = d.toordinal()
    parts = [f"☀️ <b>Доброе утро!</b>\n{LINE}\n📅 <b>{WEEKDAYS[d.weekday()]}, {d.day} {MONTHS[d.month - 1]}</b>"]
    if info.get("holiday"):
        parts.append(f"🎉 <b>Сегодня:</b> {esc(info['holiday'])}")
    parts.append(f"💡 <b>Факт дня:</b> {esc(FACTS[n % len(FACTS)])}")
    if info.get("event"):
        parts.append(f"📜 <b>В этот день:</b> {esc(info['event'])}")
    parts.append(f"🌦 {weather}" + (f"\n{rates}" if rates else ""))
    parts.append(f"📰 <b>Главное в мире:</b>\n{news}")
    parts.append(f"<i>🍀 {esc(PROVERBS[n % len(PROVERBS)])}</i>")
    return "\n\n".join(parts)


def morning_kb(uid: int) -> InlineKeyboardMarkup:
    label = "🔕 Не присылать по утрам" if pref(uid, "morning") else "🔔 Присылать по утрам"
    return _kb([("🎁 Забрать бонус", "e:bonus"), ("🧩 Вопрос дня", "e:qod")], [(label, "m:mtoggle")],
               [("⚙️ Город и время", "e:set"), ("‹ Меню", "m:home")])


# ====================== погода-карточка ======================
async def weather_card(city: str) -> str:
    async with httpx.AsyncClient(timeout=15) as c:
        place = await _geocode(c, city)
        w = (await c.get("https://api.open-meteo.com/v1/forecast", params={
            "latitude": place["latitude"], "longitude": place["longitude"],
            "current": "temperature_2m,apparent_temperature,weather_code,wind_speed_10m",
            "hourly": "temperature_2m,precipitation_probability,weather_code",
            "timezone": "auto", "forecast_days": 2,
        })).json()
    cur, h = w["current"], w["hourly"]
    i = h["time"].index(cur["time"][:13] + ":00")
    lines = [f"🌍 <b>{esc(place['name'])}</b>\n{LINE}",
             f"<b>{cur['temperature_2m']:+.0f}°</b>  {WEATHER_CODES.get(cur['weather_code'], '')}\n"
             f"<i>ощущается как {cur['apparent_temperature']:+.0f}° · ветер {cur['wind_speed_10m']:.0f} км/ч</i>",
             ""]
    for d in (2, 4, 6):
        j = i + d
        rain = h["precipitation_probability"][j] or 0
        lines.append(f"⏱ <b>{h['time'][j][11:16]}</b>  {h['temperature_2m'][j]:+.0f}° · "
                     f"{WEATHER_CODES.get(h['weather_code'][j], '')} · 💧{rain}%")
    return "\n".join(lines)


def weather_kb() -> InlineKeyboardMarkup:
    return _kb([("🔄 Обновить", "m:weather"), ("🏙 Другой город", "m:city")], [("‹ Меню", "m:home")])


async def weather_text(city: str, context=None, remember=False) -> str:
    try:
        text = await weather_card(city)
        if remember and context is not None:
            context.user_data["city"] = city
        return text
    except LookupError:
        return "Не нашёл такой город. Нажмите «Другой город» и попробуйте написать иначе."
    except Exception:
        log.exception("forecast failed")
        return "Не удалось получить прогноз, попробуйте позже."


async def send_weather(update: Update, context: ContextTypes.DEFAULT_TYPE, city: str, remember: bool = False):
    text = await weather_text(city, context, remember)
    await update.effective_message.reply_text(text, parse_mode="HTML", reply_markup=weather_kb())


async def weather_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    arg = " ".join(context.args or []).strip()[:60]
    uid = update.effective_user.id
    city = arg or context.user_data.get("city") or city_of(uid)
    await send_weather(update, context, city, remember=bool(arg))


async def morning_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    await update.effective_message.reply_text(
        await morning_text(city_of(uid)), parse_mode="HTML",
        disable_web_page_preview=True, reply_markup=morning_kb(uid))


# ====================== правда или действие (только в личке) ======================
LEVELS = ["lite", "mid", "hot"]
LEVEL_NAME = {"lite": "😊 Лёгкий", "mid": "😏 Средний", "hot": "🔥 Горячий"}
LEVEL_POOLS = {"lite": ("TRUTHS", "DARES"), "mid": ("SPICY_TRUTHS", "SPICY_DARES"), "hot": ("HOT_TRUTHS", "HOT_DARES")}


def adult_ok(uid: int) -> bool:
    """Уровни 18+ доступны владельцу и тем друзьям, кому он это разрешил."""
    return is_owner(uid) or USERS["prefs"].get(uid, {}).get("adult_ok", False)


def level_of(uid: int) -> str:
    prefs = USERS["prefs"].get(uid, {})
    if not adult_ok(uid) or not prefs.get("adult"):          # возраст не подтверждён
        return "lite"
    return prefs.get("level", "mid") if prefs.get("level") in LEVELS else "mid"


def td_kb(uid: int) -> InlineKeyboardMarkup:
    rows = [[("🗣 Правда", "game:td:truth"), ("🎬 Действие", "game:td:dare")],
            [("🎲 Случайно", "game:td:rand"), ("💡 Свой вопрос", "game:sug")]]
    if adult_ok(uid):
        rows.append([(f"🎚 Уровень: {LEVEL_NAME[level_of(uid)]}", "game:adult")])
    rows.append([("‹ Меню", "m:home")])
    return _kb(*rows)


def pick_td(kind: str, level: str) -> str:
    own = custom_pick(kind, level)
    if own:
        return own
    truths, dares = (globals()[n] for n in LEVEL_POOLS[level])
    text = random.choice(truths) if kind == "truth" else random.choice(dares)
    return text.replace("{other}", "игрока, который согласится")


def td_intro(uid: int) -> str:
    return (f"🎭 <b>Правда или действие</b>\n{LINE}\nУровень: {LEVEL_NAME[level_of(uid)]}\n"
            "<i>Выберите, что вам выпало.</i>")


async def on_game(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    uid = q.from_user.id
    if not is_allowed(uid) or q.message.chat.type != "private":
        return
    parts = q.data.split(":")
    game, arg = parts[1], (parts[2] if len(parts) > 2 else None)
    if game == "td":
        if arg is None:
            await show(q, td_intro(uid), td_kb(uid))
            return
        kind = random.choice(("truth", "dare")) if arg == "rand" else arg
        lvl = level_of(uid)
        head = "🗣 <b>Правда</b>" if kind == "truth" else "🎬 <b>Действие</b>"
        tag = {"lite": "", "mid": "🔞 ", "hot": "🔥 "}[lvl]
        text = f"{tag}{head}\n{LINE}\n{esc(pick_td(kind, lvl))}"
        if lvl != "lite":
            text += "\n\n<i>Любой игрок вправе пропустить вопрос или задание.</i>"
        await show(q, text, td_kb(uid))
    elif game == "adult":
        prefs = USERS["prefs"].setdefault(uid, {})
        if not adult_ok(uid):
            await show(q, "Этот режим для вас недоступен.", _kb([("‹ Назад", "game:td")]))
        elif not prefs.get("adult"):
            await show(q, "🔞 Уровни «Средний» и «Горячий» только для совершеннолетних: вопросы и задания будут "
                          "пикантными, а некоторые зададут игроку физический контакт по согласию. Вам есть 18 лет?",
                       _kb([("✅ Да, мне есть 18", "game:adult18:yes"), ("❌ Нет", "game:adult18:no")]))
        else:
            nxt = LEVELS[(LEVELS.index(level_of(uid)) + 1) % len(LEVELS)]
            prefs["level"] = nxt
            _save_users()
            await show(q, td_intro(uid), td_kb(uid))
    elif game == "sug":
        if arg in ("truth", "dare"):
            context.user_data["await"] = "cq:" + arg
            await show(q, "💡 Напишите ваш вопрос или задание одним сообщением (до 200 символов).\n"
                          "Если владелец одобрит, оно появится в игре, а вам +100 💰.", _kb([("‹ Назад", "game:td")]))
        else:
            await show(q, "💡 <b>Свой вопрос</b>\nЧто хотите предложить?",
                       _kb([("🗣 Правда", "game:sug:truth"), ("🎬 Действие", "game:sug:dare")], [("‹ Назад", "game:td")]))
    elif game == "adult18":
        if arg == "yes" and adult_ok(uid):
            prefs = USERS["prefs"].setdefault(uid, {})
            prefs["adult"], prefs["level"] = True, "mid"
            _save_users()
            await show(q, "🔞 Режим включён: уровень «Средний». Меняйте уровень кнопкой ниже. "
                          "Играйте только со взрослыми и по согласию: пропустить можно любой вопрос.", td_kb(uid))
        else:
            await show(q, "Хорошо, остаёмся на лёгком уровне.", td_kb(uid))


# ====================== живое меню ======================
BTN_MENU = "☰ Меню"


def reply_kb() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup([[BTN_MENU]], resize_keyboard=True, is_persistent=True,
                               input_field_placeholder="Пришлите ссылку или файл ✨")


def home_text(uid: int) -> str:
    return (f"✨ <b>Главное меню</b>\n{LINE}\n{shown(uid)}  ·  💰 {acct(uid)['coins']}\n\n"
            "<i>Просто пришлите ссылку на видео или файл, остальное я сделаю сам.</i>")


def home_kb(uid: int) -> InlineKeyboardMarkup:
    rain = "✅" if pref(uid, "rain") else "⬜"
    rows = [[("🧰 Инструменты", "m:tools"), ("🌦 Погода", "m:weather")],
            [("☀️ Сводка", "m:morning"), (f"☔ Дождь {rain}", "m:rain")],
            [("🎭 Правда или действие", "m:td"), ("⚔️ Дуэль", "d:menu")],
            [("🧩 Вопрос дня", "e:qod"), ("🏆 Рейтинг", "e:lb:w")],
            [("👤 Профиль", "e:profile"), ("💡 Помощь", "m:help")]]
    if is_owner(uid):
        rows.append([("👥 Друзья и группы", "m:friends"), ("📊 Панель", "p:home")])
    return _kb(*rows)


def welcome_text() -> str:
    file_mb = FRIEND_MAX_MB if LOCAL_API_URL else min(FRIEND_MAX_MB, 20)
    return (
        f"✨ <b>Привет! Я ваш карманный помощник</b>\n{LINE}\n"
        "📥 Ссылка TikTok, Reels или YouTube: пришлю видео, YouTube ещё и MP3\n"
        "✂️ Длинное видео или MP3 могу нарезать на части по 3, 5 или 10 минут\n"
        "🎞 Видео-файл: сожму или достану звук. Картинка: PDF, стикер или чтение QR\n"
        "🔲 /qr текст: сделаю QR-код\n"
        "🔎 В любом чате: @имя_бота и ссылка, повторное видео пришлю мгновенно\n"
        f"🌦 Погода сейчас и через 2, 4, 6 часов (по умолчанию {esc(FRIEND_CITY)})\n"
        "☀️ Утренняя карточка: праздник, факт дня, погода, курсы и новости (город и время меняются в настройках)\n"
        "☔ Предупрежу за полчаса до дождя\n"
        "🎭 Правда или действие с тремя уровнями\n"
        "🧩 Вопрос дня, монеты, бонус, достижения, магазин званий и подарки друзьям\n"
        "⚔️ Дуэли с друзьями в личке и рейтинги: общий, недельный и месячный\n"
        "🎮 Игры, казино, мафия и анонимные вопросы работают в группах: добавьте меня в чат\n\n"
        f"📋 <b>Правила и лимиты</b>\n{LINE}\n"
        f"• до {FRIEND_JOBS_PER_HOUR} скачиваний и конвертаций в час, по одной за раз\n"
        f"• видео до {FRIEND_MAX_MIN} мин и {FRIEND_MAX_MB} МБ, без прямых эфиров\n"
        f"• файлы для конвертации до {file_mb} МБ\n"
        "• ссылки только YouTube, TikTok и Instagram\n"
        "• не больше 20 сообщений в минуту\n"
        "• владелец может отозвать доступ в любой момент\n\n"
        "👇 <i>Меню откроется кнопкой «☰ Меню» внизу</i>"
    )


HELP = (
    f"💡 <b>Что я умею</b>\n{LINE}\n"
    "📥 Ссылка TikTok / Reels / YouTube: видео или MP3\n"
    "🎞 Видео-файл: сжать или вытащить MP3. Картинка: PDF, стикер, чтение QR\n"
    "🔲 /qr текст: сделать QR-код\n"
    "🌦 /weather Город: погода сейчас и через 2, 4, 6 часов\n"
    f"☀️ /morning: карточка дня (сама приходит в {MORNING_TIME})\n"
    "☔ /rain: оповещения о дожде вкл/выкл\n"
    "🎭 Правда или действие: три уровня, личная игра\n"
    "🧩 Вопрос дня, ⚔️ дуэли с друзьями, 🏆 рейтинги\n"
    "👤 Профиль: монеты, бонус, достижения, магазин, подарки, настройки\n"
    "🔎 Inline: @имя_бота и ссылка в любом чате\n\n"
    f"👑 <b>Для владельца</b>\n{LINE}\n"
    "👥 /friends: друзья и группы, 🔞 уровни\n"
    "➕ /add ID: добавить друга вручную\n"
    "📊 /panel: статистика и рассылка  ·  🗂 /backup: копия данных  ·  🔄 /update: обновить yt-dlp\n"
    "💬 В группах: /games (игры, казино, мафия, викторины, дуэли), /top (рейтинг), /ask (анонимный вопрос), "
    "/gift 100 (ответом на сообщение: подарить монеты)"
)


async def m_qr(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data["await"] = "qr"
    await update.effective_message.reply_text("🔲 Напишите текст или ссылку, и я сделаю QR-код.")


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    payload = (context.args[0] if context.args else "")
    if payload.startswith("ask_"):
        await ask_begin(update, context, payload)
        return
    if payload.startswith("inv_"):
        await on_invite_start(update, context, payload[4:])
        return
    if not is_allowed(uid):                               # гость по игровой ссылке
        await update.message.reply_text(
            "👋 Привет! Теперь я смогу присылать вам роли в играх и передавать анонимные вопросы.\n"
            "Остальные функции доступны по приглашению владельца бота.")
        return
    acct(uid, update.effective_user.full_name)
    if payload.startswith("du_"):
        await du_join(update, context, payload[3:])
        return
    if payload.startswith("dl_"):
        await start_download_by_token(update, context, payload[3:])
        return
    if payload.startswith("gift_"):
        await update.message.reply_text(cheque_claim(uid, payload[5:], update.effective_user.full_name),
                                        parse_mode="HTML")
    await update.message.reply_text("✨ Готово! Кнопка «☰ Меню» теперь внизу.", reply_markup=reply_kb())
    await update.message.reply_text(home_text(uid), parse_mode="HTML", reply_markup=home_kb(uid))


async def menu_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    context.user_data.pop("await", None)
    await update.effective_message.reply_text(home_text(uid), parse_mode="HTML", reply_markup=home_kb(uid))


async def on_menu(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    uid = q.from_user.id
    if not is_allowed(uid) or q.message.chat.type != "private":
        return
    parts = q.data.split(":")
    act = parts[1]
    ud = context.user_data
    back = _kb([("‹ Меню", "m:home")])
    if act == "home":
        ud.pop("await", None)
        await show(q, home_text(uid), home_kb(uid))
    elif act == "tools":
        await show(q, f"🧰 <b>Инструменты</b>\n{LINE}\nОбычно кнопки не нужны: просто пришлите ссылку или файл.",
                   _kb([("📥 Скачать видео", "m:t:video"), ("🎞 Конвертер", "m:t:file")],
                       [("🔲 QR-код", "m:t:qr")], [("‹ Меню", "m:home")]))
    elif act == "t":
        kind = parts[2] if len(parts) > 2 else ""
        if kind == "video":
            await show(q, "📥 <b>Скачать видео</b>\nПришлите ссылку на TikTok, Reels или YouTube.",
                       _kb([("‹ Инструменты", "m:tools")]))
        elif kind == "file":
            await show(q, "🎞 <b>Конвертер</b>\nПришлите видео (сжать или достать MP3) или картинку "
                          "(PDF, стикер, чтение QR).", _kb([("‹ Инструменты", "m:tools")]))
        elif kind == "qr":
            ud["await"] = "qr"
            await show(q, "🔲 <b>QR-код</b>\nНапишите текст или ссылку.", _kb([("‹ Инструменты", "m:tools")]))
    elif act == "weather":
        await show(q, "⏳ Смотрю прогноз…", None)
        city = ud.get("city") or city_of(uid)
        await show(q, await weather_text(city, context), weather_kb())
    elif act == "city":
        ud["await"] = "city"
        await show(q, "🏙 Напишите название города, например: Казань", back)
    elif act == "morning":
        await show(q, "⏳ Собираю карточку дня…", None)
        await show(q, await morning_text(city_of(uid)), morning_kb(uid))
    elif act == "mtoggle":
        on = not pref(uid, "morning")
        USERS["prefs"].setdefault(uid, {})["morning"] = on
        _save_users()
        try:
            await q.edit_message_reply_markup(reply_markup=morning_kb(uid))
        except Exception:
            pass
    elif act == "rain":
        on = not pref(uid, "rain")
        USERS["prefs"].setdefault(uid, {})["rain"] = on
        _save_users()
        await show(q, home_text(uid), home_kb(uid))
    elif act == "td":
        await show(q, td_intro(uid), td_kb(uid))
    elif act == "help":
        await show(q, HELP if is_owner(uid) else welcome_text(), back)
    elif act == "friends" and is_owner(uid):
        text, kb = friends_view()
        rows = list(kb.inline_keyboard) if kb else []
        rows.append([InlineKeyboardButton("‹ Меню", callback_data="m:home")])
        await show(q, text, InlineKeyboardMarkup(rows), parse=None)


async def on_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    text = (update.message.text or "").strip()
    uid = update.effective_user.id
    if not is_allowed(uid):                           # гость: только текст анонимного вопроса
        if context.user_data.get("ask"):
            await ask_submit(update, context, text)
        return
    if text == BTN_MENU:
        await menu_cmd(update, context)
        return
    mode = context.user_data.pop("await", None)       # бот ждал ответа после кнопки
    if mode == "qr":
        await send_qr(update, text)
        return
    if mode == "city":
        await send_weather(update, context, text[:60], remember=True)
        return
    if mode == "setcity":
        name = await set_city(uid, text)
        if name:
            await update.message.reply_text(f"✅ Город сохранён: {name}. Погода, дождь и утренняя карточка теперь по нему.",
                                            reply_markup=_kb([("⚙️ Настройки", "e:set"), ("‹ Меню", "m:home")]))
        else:
            await update.message.reply_text("Не нашёл такой город. Откройте «Настройки» и попробуйте написать иначе.",
                                            reply_markup=_kb([("⚙️ Настройки", "e:set")]))
        return
    if mode == "bc" and is_owner(uid):
        context.user_data["bc_text"] = text[:3000]
        await update.message.reply_text("📣 Так увидят друзья:\n\n" + text[:3000], reply_markup=_kb(
            [("✅ Отправить всем", "p:bcgo"), ("✖ Отмена", "p:bcno")]))
        return
    if mode and mode.startswith("cq:"):
        await cq_submit(update, context, mode[3:], text)
        return
    m = URL_RE.search(text)
    if not m:
        await update.message.reply_text("Пришлите ссылку или файл, либо откройте «☰ Меню».")
        return
    url = m.group(0)
    if not url_allowed(url, uid):
        await update.message.reply_text("Поддерживаются ссылки YouTube, TikTok и Instagram.")
        return
    if "youtube.com" in url or "youtu.be" in url:
        context.user_data["url"] = url
        await update.message.reply_text("Что скачать?", reply_markup=_kb(
            [("🎬 Видео", "yt:video"), ("🎵 MP3", "yt:audio")], [("✂️ Нарезать на части", "yt:cut")]))
    else:                                             # TikTok, Instagram и всё остальное
        await download_and_send(update, url)



# ====================== вопросы для групповых игр ======================
QUIZ = [
    ("Какой город является столицей Австралии?", ["Сидней", "Мельбурн", "Канберра", "Перт"], 2),
    ("Какая планета ближе всего к Солнцу?", ["Венера", "Меркурий", "Марс", "Земля"], 1),
    ("Какой химический символ у золота?", ["Ag", "Fe", "Au", "Gd"], 2),
    ("Кто написал роман «Преступление и наказание»?", ["Толстой", "Достоевский", "Чехов", "Тургенев"], 1),
    ("В каком году Юрий Гагарин полетел в космос?", ["1957", "1961", "1965", "1969"], 1),
    ("Какой океан самый большой?", ["Атлантический", "Индийский", "Северный Ледовитый", "Тихий"], 3),
    ("Сколько цветов в радуге?", ["5", "6", "7", "8"], 2),
    ("Какая страна подарила США Статую Свободы?", ["Англия", "Франция", "Италия", "Испания"], 1),
    ("Какая планета Солнечной системы самая большая?", ["Сатурн", "Юпитер", "Нептун", "Уран"], 1),
    ("Сколько струн у классической гитары?", ["4", "5", "6", "7"], 2),
    ("Кто написал картину «Мона Лиза»?", ["Микеланджело", "Рафаэль", "Леонардо да Винчи", "Ван Гог"], 2),
    ("Какой металл жидкий при комнатной температуре?", ["Свинец", "Ртуть", "Олово", "Цинк"], 1),
    ("Что измеряют в герцах?", ["Давление", "Частоту", "Мощность", "Напряжение"], 1),
    ("Какой язык программирования назван в честь британской комедийной группы?", ["Java", "Ruby", "Python", "Go"], 2),
    ("Кто автор романа «Мастер и Маргарита»?", ["Булгаков", "Пастернак", "Шолохов", "Набоков"], 0),
    ("Какой город является столицей Канады?", ["Торонто", "Монреаль", "Оттава", "Ванкувер"], 2),
    ("Сколько костей у взрослого человека?", ["186", "206", "226", "256"], 1),
    ("Какая страна самая маленькая в мире по площади?", ["Монако", "Ватикан", "Сан-Марино", "Лихтенштейн"], 1),
    ("Какой город является столицей Турции?", ["Стамбул", "Измир", "Анкара", "Анталья"], 2),
    ("Сколько секунд в часе?", ["360", "3600", "6000", "1200"], 1),
    ("В каком году вышел фильм «Титаник» Джеймса Кэмерона?", ["1995", "1997", "1999", "2001"], 1),
    ("Кто сыграл капитана Джека Воробья?", ["Орландо Блум", "Брэд Питт", "Джонни Депп", "Том Харди"], 2),
    ("Какая группа выпустила песню «Bohemian Rhapsody»?", ["The Beatles", "Queen", "Led Zeppelin", "Pink Floyd"], 1),
    ("Как называется валюта Японии?", ["Вона", "Юань", "Иена", "Рупия"], 2),
    ("Какой цвет получится при смешении синего и жёлтого?", ["Оранжевый", "Фиолетовый", "Зелёный", "Коричневый"], 2),
    ("Из чего традиционно делают текилу?", ["Из кукурузы", "Из агавы", "Из винограда", "Из сахарного тростника"], 1),
    ("Кто написал книги о Гарри Поттере?", ["Дж. Р. Р. Толкин", "Дж. К. Роулинг", "С. Кинг", "Р. Даль"], 1),
    ("Какое сухопутное животное бегает быстрее всех?", ["Лев", "Гепард", "Антилопа", "Лошадь"], 1),
    ("Сколько колец на олимпийском флаге?", ["4", "5", "6", "7"], 1),
    ("Какой газ преобладает в атмосфере Земли?", ["Кислород", "Азот", "Углекислый газ", "Аргон"], 1),
    ("Сколько хромосом у человека?", ["23", "44", "46", "48"], 2),
    ("Кто создал теорию относительности?", ["Ньютон", "Эйнштейн", "Бор", "Галилей"], 1),
    ("Какой город называют «Северной Венецией»?", ["Мурманск", "Санкт-Петербург", "Архангельск", "Калининград"], 1),
    ("Сколько минут длится основное время футбольного матча?", ["60", "80", "90", "120"], 2),
    ("Какое животное изображено на логотипе WWF?", ["Тигр", "Панда", "Слон", "Кит"], 1),
    ("Какая страна выиграла первый чемпионат мира по футболу в 1930 году?", ["Бразилия", "Аргентина", "Уругвай", "Италия"], 2),
    ("Какой город является столицей Италии?", ["Милан", "Рим", "Неаполь", "Венеция"], 1),
    ("Какой напиток получают из перебродившего виноградного сока?", ["Пиво", "Вино", "Сидр", "Виски"], 1),
    ("Какая гора считается самой высокой в мире?", ["К2", "Эльбрус", "Эверест", "Килиманджаро"], 2),
    ("Какой фильм получил «Оскар» как лучший фильм в 2020 году?", ["«Джокер»", "«1917»", "«Паразиты»", "«Ирландец»"], 2),
]
QUIZ18 = [
    ("Какой гормон часто называют «гормоном любви»?", ["Адреналин", "Окситоцин", "Инсулин", "Кортизол"], 1),
    ("Как звали греческую богиню любви и красоты?", ["Афина", "Гера", "Афродита", "Артемида"], 2),
    ("Как римляне называли богиню любви?", ["Минерва", "Юнона", "Венера", "Диана"], 2),
    ("Какую картину написал Густав Климт?", ["«Крик»", "«Поцелуй»", "«Подсолнухи»", "«Герника»"], 1),
    ("Из какой страны родом фламенко, танец страсти?", ["Португалия", "Мексика", "Испания", "Куба"], 2),
    ("Из каких ингредиентов классически делают «Маргариту»?", ["Ром, мята, лайм", "Текила, трипл сек, лайм", "Водка, клюква, лайм", "Джин, тоник, лимон"], 1),
    ("На каком древнем языке написана «Камасутра»?", ["На латыни", "На санскрите", "На древнегреческом", "На арабском"], 1),
    ("Кто написал трагедию «Ромео и Джульетта»?", ["Мольер", "Шекспир", "Гёте", "Данте"], 1),
    ("В какой стране находится кабаре «Мулен Руж»?", ["Италия", "Германия", "Франция", "Бельгия"], 2),
    ("Какой плод по традиции называют запретным плодом из райского сада?", ["Яблоко", "Груша", "Гранат", "Апельсин"], 0),
    ("Что по традиции делают под омелой на Рождество?", ["Загадывают желание", "Целуются", "Танцуют", "Поют"], 1),
    ("Какой праздник отмечают 14 февраля?", ["День влюблённых", "День матери", "Хэллоуин", "День труда"], 0),
    ("Что означает французское выражение «le coup de foudre»?", ["Любовь с первого взгляда", "Ссора влюблённых", "Первое свидание", "Разбитое сердце"], 0),
    ("Какой итальянский город связан с именем Казановы?", ["Рим", "Венеция", "Флоренция", "Турин"], 1),
]
WHO = [
    "Кто скорее всего опоздает на собственную свадьбу?", "Кто скорее всего выиграет в лотерею и потеряет билет?",
    "Кто скорее всего влюбится с первого взгляда?", "Кто скорее всего заснёт на вечеринке?",
    "Кто скорее всего станет миллионером?", "Кто скорее всего забудет день рождения лучшего друга?",
    "Кто скорее всего переедет в другую страну?", "Кто скорее всего напишет бывшему ночью?",
    "Кто скорее всего расплачется на комедии?", "Кто скорее всего заведёт десять котов?",
    "Кто скорее всего первым женится или выйдет замуж?", "Кто скорее всего станет знаменитым?",
    "Кто скорее всего проспит важную встречу?", "Кто скорее всего сядет в самолёт не в ту сторону?",
    "Кто скорее всего подружится с незнакомцем в очереди?", "Кто скорее всего потеряет телефон в этом месяце?",
    "Кто скорее всего споёт в караоке громче всех?", "Кто скорее всего устроит сюрприз-вечеринку?",
    "Кто скорее всего сбежит с лекции или работы ради приключения?", "Кто скорее всего начнёт свой бизнес?",
    "Кто скорее всего будет флиртовать с официантом?", "Кто скорее всего первым заговорит о политике за столом?",
    "Кто скорее всего влюбится в героя сериала?", "Кто скорее всего устроит драму на ровном месте?",
    "Кто скорее всего пойдёт на свидание вслепую?", "Кто скорее всего целуется лучше всех?",
    "Кто скорее всего расскажет чужой секрет и сразу пожалеет?", "Кто скорее всего ответит на сообщение через три дня?",
    "Кто скорее всего согласится на дерзкий спор?", "Кто скорее всего станцует на столе?",
    "Кто скорее всего вернётся с отпуска с новой любовью?", "Кто скорее всего сделает татуировку на спор?",
]



# ====================== правда или действие: вопросы ======================
TRUTHS = [
    "Какая самая неловкая ситуация случалась с тобой в школе?",
    "Что самое странное ты когда-либо гуглил(а)?",
    "Какую песню ты слушаешь, но стесняешься в этом признаться?",
    "Какой самый странный сон тебе снился?",
    "Чего ты боишься, хотя это звучит смешно?",
    "Какой фильм ты пересматривал(а) больше всего раз?",
    "Что ты чаще всего откладываешь на потом?",
    "Какую суперсилу ты бы выбрал(а) и как бы использовал(а) её в быту?",
    "Какая у тебя самая глупая импульсивная покупка?",
    "Какая профессия была у тебя в детстве «мечтой»?",
    "Какую привычку ты хотел(а) бы поменять?",
    "Какой самый неловкий разговор с незнакомцем у тебя был?",
    "Что ты делаешь, когда думаешь, что никто не видит?",
    "Какой подарок ты получил(а) и тайно не оценил(а)?",
    "Какую ложь ты говоришь чаще всего?",
    "Если бы можно было на день поменяться жизнями с кем-то из знакомых, то с кем и почему?",
    "Какое самое позднее пробуждение у тебя было и во сколько?",
    "Какую песню ты поёшь в душе?",
    "Какой навык ты хотел(а) бы освоить за один день?",
    "Какая еда тебе нравится, а другим кажется странной?",
]
DARES = [
    "Изобрази походку любого животного на 30 секунд.",
    "Говори голосом робота следующие 3 минуты.",
    "Сделай 10 приседаний, считая по-английски.",
    "Станцуй 20 секунд под любую песню.",
    "Придумай смешную историю из трёх предложений про ближайший предмет.",
    "Покажи своё лучшее «лицо из мема».",
    "Сделай комплимент каждому, кто рядом.",
    "Спой куплет любой песни в стиле оперы.",
    "Говори только вопросами следующие 2 минуты.",
    "Нарисуй кота с закрытыми глазами и покажи всем.",
    "Опиши любимый фильм только эмодзи, пусть остальные угадывают.",
    "Простой на одной ноге 30 секунд.",
    "Скажи скороговорку про Карла и Клару три раза быстро.",
    "Изобрази сцену из известного фильма, остальные угадывают.",
    "Не используй букву «а» в речи две минуты.",
    "Назови 10 фруктов за 15 секунд.",
    "Пройдись по комнате как модель на подиуме.",
    "Сделай селфи с самым смешным выражением лица и покажи всем.",
    "Расскажи анекдот. Если никто не засмеялся, повтори другой интонацией.",
    "Произнеси тост за самый обычный предмет в комнате.",
]
TRUTHS += [
    "Какой самый странный подарок ты дарил(а)?",
    "В каком деле ты самый большой «тормоз»?",
    "Какую вещь ты хранишь в шкафу, хотя давно пора выбросить?",
    "Какую глупую причину опоздания ты придумывал(а)?",
    "Какой у тебя самый бесполезный навык?",
    "С каким животным ты себя ассоциируешь и почему?",
    "В какую страну ты бы переехал(а) и почему?",
    "Что бы ты сделал(а), если бы на один день получил(а) миллион?",
    "Какой самый странный совет ты получал(а)?",
    "О чём ты жалеешь больше всего?",
    "Какой самый смешной случай был у тебя на работе или учёбе?",
    "Какая вредная привычка у тебя самая «любимая»?",
    "Что бы ты сказал(а) себе десятилетнему?",
    "Какой у тебя самый эпичный кулинарный провал?",
    "Из-за какой глупости ты ссорился(ась) с близкими?",
    "Что в тебе самое странное, но тебе это нравится?",
    "Какую фразу из мультика ты цитируешь чаще всего?",
    "Сколько часов максимум ты не выпускал(а) телефон из рук?",
    "За какое дело ты берёшься, хотя не умеешь?",
    "Какой самый смешной прикол ты устраивал(а) над друзьями?",
    "Что ты возьмёшь на необитаемый остров, кроме телефона?",
    "Какое слово ты постоянно произносишь неправильно?",
    "Какой самый смешной сон про знакомого человека тебе снился?",
    "Что тебе нравилось в детстве, а теперь кажется странным?",
    "Какой самый нелепый повод для радости у тебя был?",
]
DARES += [
    "Покажи, как ты будешь выступать на вручении «Оскара», получив награду.",
    "Прочитай любое стихотворение с интонацией диктора новостей.",
    "Изобрази ведущего прогноза погоды и расскажи о погоде в комнате.",
    "Передразни любого игрока, остальные угадывают, кого именно.",
    "Построй башню из подручных предметов за 30 секунд.",
    "Станцуй так, как будто на дворе 80-е.",
    "Изобрази кота, которого не пустили на кухню.",
    "Пройди по комнате с книгой на голове.",
    "Серьёзно сделай комплимент своему отражению.",
    "Разыграй ссору двух предметов на столе.",
    "Назови пять столиц за 10 секунд.",
    "Изобрази тренера по фитнесу, объясняющего упражнение.",
    "Торжественно объяви меню завтрашнего обеда.",
    "Нарисуй автопортрет за 30 секунд левой рукой.",
    "Изобрази робота, который сломался.",
    "Придумай рекламу самого обычного предмета рядом.",
    "Говори с акцентом следующие две минуты.",
    "Изобрази утку, которая учится плавать.",
    "Расскажи историю из трёх предложений, где каждое начинается со следующей буквы алфавита.",
    "Покажи, как выглядит человек, которому только что сказали хорошую новость.",
]
SPICY_TRUTHS = [
    "Какой самый смелый флирт был в твоей жизни?",
    "Какое самое пикантное сообщение ты отправлял(а)?",
    "В каком самом необычном месте ты целовался(ась)?",
    "Что заводит тебя в человеке сильнее всего: голос, руки, запах или юмор?",
    "Какое самое неловкое свидание у тебя было?",
    "Какое пикантное прозвище тебе когда-нибудь давали?",
    "Какой самый безумный поступок ты совершил(а) ради симпатии?",
    "За какой поцелуй ты потом жалел(а)?",
    "Каким ты представляешь самое идеальное свидание, от начала до конца?",
    "На какую часть тела ты обращаешь внимание у человека в первую очередь?",
    "Какой самый смелый наряд ты надевал(а) и по какому поводу?",
    "Кому из знакомых ты отправил(а) бы ночью «скучаю»?",
    "Что необычное кажется тебе сексуальным?",
    "Был(а) ли у тебя роман на одну ночь? Расскажи без подробностей.",
    "Какую самую пошлую шутку ты когда-либо рассказывал(а)?",
    "Если бы пришлось застрять в лифте с кем-то из присутствующих, то с кем?",
    "Какая сцена в фильме тебя сильно смутила, когда ты смотрел(а) его с родителями?",
    "Какие пикантные эмодзи ты отправляешь чаще всего?",
    "В каком месте ты ещё не целовался(ась), но очень хотел(а) бы?",
    "Присылал(а) ли ты откровенное сообщение не тому человеку? Что было дальше?",
    "Что для тебя самое сексуальное в одежде?",
    "Какой комплимент действует на тебя сильнее всего?",
    "Согласился(ась) бы ты на «дружбу с привилегиями»? Почему?",
    "Какую роль ты выбрал(а) бы для ролевой игры?",
    "Какой самый горячий момент в твоей жизни ты можешь рассказать здесь?",
    "Какой самый откровенный сон ты видел(а)? Без имён, только сюжет.",
    "Что ты скажешь незнакомцу, чтобы очаровать его за десять секунд?",
    "Оцени свои поцелуи по десятибалльной шкале. Почему именно столько?",
    "Какая самая нелепая подкатка была в твою сторону?",
    "Какая самая нелепая подкатка была от тебя?",
    "Кто из присутствующих показался тебе самым привлекательным при знакомстве?",
    "О чём ты фантазируешь перед сном?",
    "Что ты делаешь, чтобы произвести впечатление на того, кто нравится?",
    "Какая песня у тебя ассоциируется с самой горячей ночью?",
    "Что бы ты сделал(а), если бы на сутки стал(а) невидимым(ой)? Самый пикантный вариант.",
    "Какое твоё самое смелое желание, о котором ты никому не рассказывал(а)?",
    "С кем из знаменитостей ты бы провёл(а) ночь?",
    "Как быстро после знакомства допустим первый поцелуй?",
    "Какой запах сводит тебя с ума?",
    "Что тебя больше всего смущает в близости?",
]
SPICY_DARES = [
    "Сделай самый соблазнительный взгляд за 10 секунд, остальные поставят оценку от 1 до 10.",
    "Пройдись по комнате самой соблазнительной походкой.",
    "Прошепчи любое слово так, чтобы оно прозвучало как можно пикантнее.",
    "Сделай игроку, который согласится, массаж плеч на 30 секунд.",
    "Скажи самую пошлую подкатку, которую знаешь, любому игроку.",
    "Изобрази страстный поцелуй с предметом, который выберет группа.",
    "Станцуй медленный танец с воображаемым партнёром 30 секунд.",
    "Сделай такой комплимент соседу слева, чтобы он покраснел.",
    "Сочини и зачитай пикантное четверостишие про соседа справа.",
    "Говори хриплым соблазнительным голосом следующие три минуты.",
    "Пусть группа придумает тебе пикантное прозвище, и откликайся только на него до конца игры.",
    "Покажи, как ты делаешь селфи для профиля в приложении знакомств.",
    "Сыграй сцену признания в любви тому, кого выберет группа.",
    "Подмигни каждому игроку по очереди как можно эффектнее.",
    "Расскажи самую пикантную историю из жизни, которую можешь рассказать без имён.",
    "Назови по три качества, которые тебе нравятся в каждом игроке.",
    "Станцуй страстное танго с подушкой.",
    "Съешь яблоко или банан максимально соблазнительно.",
    "Изобрази, как ты встречаешь любимого человека после долгой разлуки, как в мелодраме.",
    "Покажи свой лучший «взгляд сквозь ресницы» и подержи его 10 секунд.",
    "Придумай и произнеси самый горячий тост этого вечера.",
    "Изобрази самый эффектный выход в халате на красную дорожку.",
    "Опиши любого игрока (кроме себя) в трёх пикантных словах.",
    "Расскажи на ухо соседу самый смелый комплимент, а остальные пусть угадывают, что ты сказал(а).",
    "Устрой мини-конкурс: пусть остальные проголосуют, кто здесь самый обаятельный. Скажи тост победителю.",
]
HOT_TRUTHS = [
    "Кого из присутствующих ты поцеловал(а) бы не раздумывая и почему?",
    "Какой самый горячий поцелуй был в твоей жизни?",
    "Что ты надеваешь, когда хочешь выглядеть максимально соблазнительно?",
    "Где тебе больше всего нравится, когда тебя целуют: шея, руки, губы?",
    "Расскажи о самом откровенном сообщении, которое ты получал(а).",
    "Какие прикосновения нравятся тебе больше всего?",
    "Хотел(а) ли ты когда-нибудь поцеловать кого-то из этой компании?",
    "Какое самое смелое, что ты делал(а) на свидании?",
    "Что должно произойти на первом свидании, чтобы ты захотел(а) второе?",
    "Что для тебя важнее в близости: нежность или страсть?",
    "Какая подкатка у тебя срабатывала лучше всего?",
    "Какой самый неловкий момент случался у тебя во время поцелуя?",
    "С кем из этой компании ты бы поехал(а) в отпуск вдвоём?",
    "Кто из этой компании, по-твоему, лучше всех целуется и почему так думаешь?",
    "Что тебя в партнёре заводит больше всего?",
    "Опиши идеальный поцелуй.",
    "Какая фраза мгновенно располагает тебя к человеку?",
    "Какой самый пикантный комплимент ты получал(а)?",
    "Какую часть собственного тела ты любишь больше всего?",
    "Сколько раз ты влюблялся(лась) в кого-то из этой компании? Без имён, только число.",
    "Какое романтичное свидание ты бы организовал(а) для человека из этой компании?",
    "Какая твоя самая смелая ночная фантазия, о которой можно рассказать при всех?",
    "Что ты сделал(а) бы, если бы точно знал(а), что никто не осудит?",
    "Какую соблазнительную фразу ты бы шепнул(а) в идеальный момент?",
    "Когда ты в последний раз краснел(а) от пикантной шутки?",
]
HOT_DARES = [
    "Поцелуй в щёку {other}.",
    "Поцелуй руку {other}, как в кино.",
    "Смотри в глаза {other} 20 секунд и не смейся.",
    "Прошепчи {other} на ухо самый смелый комплимент.",
    "Сними одну вещь по выбору группы: носок, аксессуар или верхнюю одежду.",
    "Станцуй медленный танец вплотную с {other}, пока группа считает до 20.",
    "Поцелуй в плечо {other}, если он(а) согласен(на).",
    "Сделай {other} массаж шеи на одну минуту.",
    "Поцелуй в губы {other} на 5 секунд, если оба согласны. Если нет, пошли воздушный поцелуй.",
    "Накорми {other} с руки чем-нибудь съедобным как можно соблазнительнее.",
    "Закрой глаза и угадай по прикосновению к руке, кто из игроков тебя коснулся.",
    "Сыграй страстную сцену из мелодрамы вместе с {other}.",
    "Расскажи {other} на ухо, что тебе в нём(ней) нравится, а потом поменяйтесь.",
    "Нарисуй {other} на руке сердечко маркером или помадой.",
    "Станцуй для всех «танец соблазна» 30 секунд, ничего не снимая.",
    "Подмигни каждому игроку и подари воздушный поцелуй тому, кто понравился больше.",
    "Пусть группа выберет, кто из вас с {other} снимет носок. Снимаете оба.",
    "Покажи {other} свой самый соблазнительный взгляд и дождись реакции.",
    "Обними {other} крепко и не отпускай 15 секунд.",
    "Сделай комплимент каждому игроку, глядя в глаза, и обними того, кого выберешь.",
    "Сядь рядом с {other}, возьми за руку и признайся в чём-нибудь пикантном.",
    "Сыграй сцену первого свидания с {other}: знакомство, комплимент, прощание.",
    "Расскажи самую смелую историю про свидание, которую не жалко рассказать.",
    "Поцелуй в щёку каждого игрока по очереди, если они согласны.",
    "Пусть {other} выберет тебе пикантное прозвище, и откликайся на него до конца игры.",
]

async def on_media(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg = update.message
    context.user_data.pop("await", None)
    if msg.video:
        context.user_data["fid"] = msg.video.file_id
        buttons = [("📉 Сжать", "conv:compress"), ("🎵 В MP3", "conv:mp3")]
    elif msg.photo:
        context.user_data["fid"] = msg.photo[-1].file_id
        buttons = [("📄 В PDF", "conv:pdf"), ("🎭 Стикер", "conv:sticker"), ("🔲 Читать QR", "conv:qrread")]
    elif msg.document and (msg.document.mime_type or "").startswith("image/"):
        context.user_data["fid"] = msg.document.file_id
        buttons = [("📄 В PDF", "conv:pdf"), ("🎭 Стикер", "conv:sticker"), ("🔲 Читать QR", "conv:qrread")]
    else:
        await msg.reply_text("Такой формат пока не поддерживаю.")
        return
    kb = InlineKeyboardMarkup([[InlineKeyboardButton(t, callback_data=d) for t, d in buttons]])
    await msg.reply_text("Что сделать?", reply_markup=kb)


async def on_button(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    if not is_allowed(q.from_user.id):
        return
    kind, action = q.data.split(":")
    if kind == "yt":
        url = context.user_data.get("url")
        if not url:
            await q.message.reply_text("Ссылка устарела, пришлите её ещё раз.")
        elif action == "cut":
            await show(q, "✂️ На какие части нарезать?\nКаждая часть придёт отдельным сообщением.", _kb(
                [("🎬 по 3 мин", "yt:v3"), ("🎬 по 5 мин", "yt:v5"), ("🎬 по 10 мин", "yt:v10")],
                [("🎵 по 3 мин", "yt:a3"), ("🎵 по 5 мин", "yt:a5"), ("🎵 по 10 мин", "yt:a10")]))
        elif len(action) > 1 and action[0] in "va" and action[1:] in ("3", "5", "10"):
            await download_and_send(update, url, audio=(action[0] == "a"), cut_min=int(action[1:]))
        elif action in ("video", "audio"):
            await download_and_send(update, url, audio=(action == "audio"))
    else:
        await convert(update, context, action)


async def _approve(context: ContextTypes.DEFAULT_TYPE, uid: int, name: str):
    USERS["approved"][uid] = name
    USERS["blocked"].pop(uid, None)
    PENDING.pop(uid, None)
    DENIED.pop(uid, None)
    _save_users()
    try:
        await context.bot.send_message(uid, "✅ <b>Владелец принял вашу заявку!</b>\n\n" + welcome_text(),
                                       parse_mode="HTML", reply_markup=reply_kb())
        await context.bot.send_message(uid, home_text(uid), parse_mode="HTML", reply_markup=home_kb(uid))
    except Exception:
        log.exception("не удалось отправить приветствие")
    invite_on_approve(uid, name)


async def on_access(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Кнопки владельца: принять, отклонить, заблокировать, удалить, разблокировать."""
    q = update.callback_query
    await q.answer()
    if not is_owner(q.from_user.id):
        return
    _, action, raw = q.data.split(":")
    uid = int(raw)
    name = NAMES.get(uid) or USERS["approved"].get(uid) or USERS["blocked"].get(uid) or f"ID {uid}"
    if action == "ok":
        if uid in USERS["approved"]:
            await q.edit_message_text(f"✅ Уже принят: {name} (ID {uid})")
            return
        await _approve(context, uid, name)
        await q.edit_message_text(f"✅ Принят: {name} (ID {uid}). Приветствие с правилами отправлено.")
    elif action == "no":
        PENDING.pop(uid, None)
        DENIED[uid] = time_module.time()
        await q.edit_message_text(f"❌ Отклонён: {name} (ID {uid})")
        try:
            await context.bot.send_message(uid, "Владелец отклонил заявку. Повторить можно через сутки.")
        except Exception:
            pass
    elif action == "ban":
        PENDING.pop(uid, None)
        USERS["approved"].pop(uid, None)
        USERS["blocked"][uid] = name
        _save_users()
        await q.edit_message_text(f"🚫 Заблокирован: {name} (ID {uid}). Бот будет его игнорировать.")
    elif action == "del":
        USERS["approved"].pop(uid, None)
        _save_users()
        await q.edit_message_text(f"🗑 Доступ убран: {name} (ID {uid})")
        try:
            await context.bot.send_message(uid, "Владелец закрыл вам доступ к боту.")
        except Exception:
            pass
    elif action == "gok":
        title = GROUP_PENDING.pop(uid, None) or f"чат {uid}"
        USERS["groups"][uid] = title
        _save_users()
        await q.edit_message_text(f"✅ Группа разрешена: {title}")
        try:
            await context.bot.send_message(uid, GROUP_HELLO, parse_mode="HTML")
        except Exception:
            log.exception("не удалось написать в группу")
    elif action == "gno":
        GROUP_PENDING.pop(uid, None)
        title = USERS["groups"].pop(uid, None)
        _save_users()
        await q.edit_message_text(f"🚪 Вышел из группы {title or uid}")
        try:
            await context.bot.leave_chat(uid)
        except Exception:
            log.exception("не удалось выйти из группы")
    elif action == "adult":
        prefs = USERS["prefs"].setdefault(uid, {})
        prefs["adult_ok"] = not prefs.get("adult_ok", False)
        if not prefs["adult_ok"]:
            prefs["adult"] = False
        _save_users()
        text, kb = friends_view()
        await q.edit_message_text(text, reply_markup=kb)
    elif action == "unban":
        USERS["blocked"].pop(uid, None)
        _save_users()
        await q.edit_message_text(f"🔓 Разблокирован: {name} (ID {uid}). Он может подать заявку снова.")


def friends_view():
    rows, lines = [], []

    def adult_btn(uid: int) -> InlineKeyboardButton:
        on = USERS["prefs"].get(uid, {}).get("adult_ok", False)
        return InlineKeyboardButton("🔞 18+: " + ("да" if on else "нет"), callback_data=f"acc:adult:{uid}")

    for uid, name in USERS["approved"].items():
        lines.append(f"• {name} (ID {uid})")
        rows.append([InlineKeyboardButton(f"🗑 {name[:18]}", callback_data=f"acc:del:{uid}"), adult_btn(uid)])
    for uid in sorted(ENV_ALLOWED):
        lines.append(f"• ID {uid} (из настроек Railway, убрать можно только там)")
        rows.append([adult_btn(uid)])
    blocked = []
    for uid, name in USERS["blocked"].items():
        blocked.append(f"• {name} (ID {uid})")
        rows.append([InlineKeyboardButton(f"🔓 Разблокировать: {name[:20]}", callback_data=f"acc:unban:{uid}")])
    for gid, gtitle in USERS["groups"].items():
        rows.append([InlineKeyboardButton(f"🚪 Выйти из: {gtitle[:22]}", callback_data=f"acc:gno:{gid}")])
    text = "👥 Друзья:\n" + ("\n".join(lines) if lines else "пока никого")
    if USERS["groups"]:
        text += "\n\n💬 Группы:\n" + "\n".join(f"• {t}" for t in USERS["groups"].values())
    if blocked:
        text += "\n\n🚫 Заблокированные:\n" + "\n".join(blocked)
    text += f"\n\nЗаявок в ожидании: {len(PENDING)}\n🔞 18+: разрешает друзьям режим 18+ в игре «Правда или действие»."
    return text, (InlineKeyboardMarkup(rows) if rows else None)


async def friends_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    text, kb = friends_view()
    await update.message.reply_text(text, reply_markup=kb)


async def add_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    arg = (context.args[0] if context.args else "").strip()
    if not arg.isdigit():
        await update.message.reply_text("Напишите так: /add 123456789")
        return
    uid = int(arg)
    await _approve(context, uid, NAMES.get(uid) or f"ID {uid}")
    await update.message.reply_text(f"✅ Добавлен ID {uid}. Если человек ещё не запускал бота, "
                                    "приветствие не дойдёт: пусть сначала нажмёт «Запустить».")





# ====================== игры для групп ======================
GG: dict[tuple[int, int], dict] = {}              # (чат, сообщение) -> состояние игры
GROUP_PENDING: dict[int, str] = {}                # группы, ждущие решения владельца
GROUP_HELLO = (f"👋 <b>Привет! Я бот с играми для компании.</b>\n{LINE}\n"
               "🎮 /games: игры, казино, мафия, викторины, дуэли\n🏆 /top: рейтинг группы и общий\n🎁 /gift 100: подарить монеты (ответом на сообщение)\n"
               "💌 /ask: анонимный вопрос (ответом на сообщение человека)\n\n"
               "<i>Чтобы я знал, кто в компании, нажмите «🙋 Я в компании» в меню /games.</i>")


def gg_put(key: tuple[int, int], st: dict):
    if len(GG) > 300:
        GG.pop(next(iter(GG)))
    GG[key] = st


def cands(chat_id: int, exclude: tuple = ()) -> list[tuple[int, str]]:
    d = dict(SEEN.get(chat_id, {}))
    for uid, r in STATS["group"].get(chat_id, {}).items():
        d.setdefault(uid, r["name"])
    return [(u, n) for u, n in list(d.items())[-12:] if u not in exclude]


def games_kb() -> InlineKeyboardMarkup:
    return _kb([("✂️ Дуэль КНБ", "gg:new:rps"), ("🗳 Кто скорее всего", "gg:new:who")],
               [("🧠 Викторина", "gg:new:quiz"), ("🔞 Викторина 18+", "gg:new:quiz18")],
               [("⚔️ Дуэль эрудитов", "gg:new:duel"), ("🎰 Казино", "gg:casino")],
               [("🕵️ Мафия", "gg:new:mafia"), ("💌 Анонимный вопрос", "gg:askmenu")],
               [("🎁 Бонус", "e:bonus"), ("🏆 Рейтинг", "gg:lb:g:w")],
               [("🙋 Я в компании", "gg:here")])


GAMES_TITLE = f"🎮 <b>Игры для компании</b>\n{LINE}\nВыбирайте, во что играем:"


async def games_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(GAMES_TITLE, parse_mode="HTML", reply_markup=games_kb())


async def group_help(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(GROUP_HELLO, parse_mode="HTML", reply_markup=games_kb())


async def top_group_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    cid = update.effective_chat.id
    await update.effective_message.reply_text(lb_text("w", cid), parse_mode="HTML", reply_markup=lb_kb("gg:lb:g:", "w", "g"))


async def top_private(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(lb_text("w"), parse_mode="HTML", reply_markup=lb_kb("e:lb:", "w"))


async def edit_key(bot, key: tuple[int, int], text: str, kb=None):
    try:
        await bot.edit_message_text(text, chat_id=key[0], message_id=key[1], parse_mode="HTML",
                                    reply_markup=kb, disable_web_page_preview=True)
    except Exception as e:
        if "not modified" not in str(e).lower():
            log.warning("не удалось обновить игру: %s", e)


# --- дуэль камень-ножницы-бумага
RPS = {"r": "🪨 Камень", "s": "✂️ Ножницы", "p": "📄 Бумага"}
RPS_BEATS = {"r": "s", "s": "p", "p": "r"}


def rps_text(st: dict) -> str:
    p1, p2 = st["p1"][1], st["p2"][1] if st["p2"] else None
    if p2 is None:
        return f"✂️ <b>Дуэль КНБ</b>\n{LINE}\n{esc(p1)} вызывает на дуэль! Кто примет вызов?"
    chosen = lambda uid: "✅ выбрал(а)" if uid in st["choices"] else "⏳ думает"
    return (f"✂️ <b>Дуэль КНБ</b>\n{LINE}\n{esc(p1)}: {chosen(st['p1'][0])}\n{esc(p2)}: {chosen(st['p2'][0])}\n\n"
            "<i>Выбор видите только вы.</i>")


RPS_PICK_KB = lambda: _kb([("🪨 Камень", "gg:pick:r"), ("✂️ Ножницы", "gg:pick:s"), ("📄 Бумага", "gg:pick:p")])


async def gg_rps(q, ctx, st, action, args):
    user = q.from_user
    arg = args[0] if args else None
    players = [st["p1"][0]] + ([st["p2"][0]] if st["p2"] else [])
    if action == "join":
        if st["p2"] is not None or user.id == st["p1"][0]:
            await q.answer("Вызов уже принят" if st["p2"] else "Нужен соперник, а не вы 🙂", show_alert=True)
            return
        st["p2"] = (user.id, _name(user))
        await q.answer()
        await show(q, rps_text(st), RPS_PICK_KB())
    elif action == "pick" and arg in RPS:
        if user.id not in players or st["p2"] is None:
            await q.answer("Вы не участвуете в дуэли" if user.id not in players else "Ждём соперника", show_alert=True)
            return
        if st.get("done"):
            await q.answer("Раунд закончен, нажмите «Реванш»")
            return
        st["choices"][user.id] = arg
        await q.answer(f"Вы выбрали {RPS[arg]}")
        if len(st["choices"]) < 2:
            await show(q, rps_text(st), RPS_PICK_KB())
            return
        (u1, n1), (u2, n2) = st["p1"], st["p2"]
        c1, c2 = st["choices"][u1], st["choices"][u2]
        if c1 == c2:
            verdict = "🤝 Ничья!"
        else:
            win_id, win_name = (u1, n1) if RPS_BEATS[c1] == c2 else (u2, n2)
            reward(q.message.chat.id, win_id, win_name, 50, game="rps")
            verdict = f"🏆 Победил(а): <b>{shown(win_id, win_name)}</b> (+50 💰)"
        st["done"] = True
        await show(q, f"✂️ <b>Дуэль КНБ</b>\n{LINE}\n{esc(n1)}: {RPS[c1]}\n{esc(n2)}: {RPS[c2]}\n\n{verdict}",
                   _kb([("🔁 Реванш", "gg:again"), ("‹ Игры", "gg:menu")]))
    elif action == "again":
        if user.id not in players or not st.get("done"):
            await q.answer("Реванш для участников после раунда", show_alert=True)
            return
        st["choices"], st["done"] = {}, False
        await q.answer()
        await show(q, rps_text(st), RPS_PICK_KB())


# --- кто скорее всего
def who_text(st: dict) -> str:
    return (f"🗳 <b>Кто скорее всего…</b>\n{LINE}\n{esc(st['q'])}\n\n"
            f"<i>Голосуйте кнопками. Проголосовало: {len(st['votes'])}. Ведущий: {esc(st['host_name'])}.</i>")


def who_kb(st: dict) -> InlineKeyboardMarkup:
    btns = [(n[:14], f"gg:wv:{u}") for u, n in st["cands"]]
    rows = [btns[i:i + 2] for i in range(0, len(btns), 2)]
    rows.append([("🏁 Итоги", "gg:wend")])
    return _kb(*rows)


async def gg_who(q, ctx, st, action, args):
    user = q.from_user
    if action == "wv" and args and args[0].lstrip("-").isdigit():
        target = int(args[0])
        if target not in dict(st["cands"]):
            await q.answer()
            return
        if target == user.id:
            await q.answer("За себя голосовать нельзя 🙂", show_alert=True)
            return
        if user.id in st["votes"]:
            await q.answer("Вы уже проголосовали", show_alert=True)
            return
        st["votes"][user.id] = target
        await q.answer(f"Голос за {dict(st['cands'])[target]} принят")
        await show(q, who_text(st), who_kb(st))
    elif action == "wend":
        if user.id not in (st["host"], OWNER_ID):
            await q.answer("Итоги подводит ведущий", show_alert=True)
            return
        if len(st["votes"]) < 2:
            await q.answer("Нужно хотя бы два голоса", show_alert=True)
            return
        await q.answer()
        tally: dict[int, int] = defaultdict(int)
        for t in st["votes"].values():
            tally[t] += 1
        top = max(tally.values())
        winners = [u for u, c in tally.items() if c == top]
        names = dict(st["cands"])
        for u in winners:
            add_coins(u, 30, names.get(u))
        for voter, t in st["votes"].items():
            if t in winners:
                add_coins(voter, 10)
        lines = "\n".join(f"{shown(u, names[u])} — {c}" for u, c in sorted(tally.items(), key=lambda x: -x[1]))
        GG.pop((q.message.chat.id, q.message.message_id), None)
        await show(q, f"🗳 <b>Кто скорее всего…</b>\n{LINE}\n{esc(st['q'])}\n\n{lines}\n\n"
                      f"🏆 Больше всех голосов: {', '.join(shown(u, names[u]) for u in winners)} (+30 💰)\n"
                      "<i>Кто угадал большинство, получил +10 💰.</i>", _kb([("‹ Игры", "gg:menu")]))


# --- викторина и дуэль эрудитов
def prep_q(item):
    text, opts, ans = item
    pairs = list(enumerate(opts))
    random.shuffle(pairs)
    return text, [o for _, o in pairs], [i for i, (old, _) in enumerate(pairs) if old == ans][0]


QUIZ_SECONDS = 20


def quiz_question_text(st: dict) -> str:
    tag = {"quiz": "🧠 Викторина", "quiz18": "🔞 Викторина 18+", "duel": "⚔️ Дуэль эрудитов"}[st["kind"]]
    text, _, _ = st["qs"][st["i"]]
    return (f"<b>{tag}</b>  ·  вопрос {st['i'] + 1}/{len(st['qs'])}\n{LINE}\n{esc(text)}\n\n"
            f"<i>⏱ {QUIZ_SECONDS} секунд. Ответ можно дать один раз.</i>")


def quiz_kb(st: dict) -> InlineKeyboardMarkup:
    _, opts, _ = st["qs"][st["i"]]
    return _kb(*[[(f"{'ABCD'[k]}. {o}", f"gg:qa:{st['i']}:{k}")] for k, o in enumerate(opts)])


async def quiz_next(bot, key, delay: float = 0):
    if delay:
        await asyncio.sleep(delay)
    st = GG.get(key)
    if st is None:
        return
    st["i"] += 1
    if st["i"] >= len(st["qs"]):
        await quiz_finish(bot, key)
        return
    st["answers"], st["revealing"] = {}, False
    await edit_key(bot, key, quiz_question_text(st), quiz_kb(st))
    spawn(quiz_timer(bot, key, st["i"]))


async def quiz_timer(bot, key, i):
    await asyncio.sleep(QUIZ_SECONDS)
    await quiz_reveal(bot, key, i)


async def quiz_reveal(bot, key, i):
    st = GG.get(key)
    if st is None or st["i"] != i or st["revealing"]:
        return
    st["revealing"] = True
    text, opts, ans = st["qs"][i]
    good = sorted([(t, u) for u, (k, t) in st["answers"].items() if k == ans])
    for n, (_, u) in enumerate(good):
        st["scores"][u] = st["scores"].get(u, 0) + 10 + (5 if n == 0 else 0)
    who = ", ".join(esc(st["names"][u]) for _, u in good) or "никто"
    await edit_key(bot, key, f"<b>Ответ</b>\n{LINE}\n{esc(text)}\n\n✅ <b>{esc(opts[ans])}</b>\n\nВерно ответили: {who}")
    await quiz_next(bot, key, delay=4)


async def quiz_finish(bot, key):
    st = GG.pop(key, None)
    if st is None:
        return
    chat = key[0]
    names, scores = st["names"], st["scores"]
    if st["kind"] == "duel":
        (u1, n1), (u2, n2) = st["p1"], st["p2"]
        s1, s2 = scores.get(u1, 0), scores.get(u2, 0)
        if s1 == s2:
            add_coins(u1, st["stake"])
            add_coins(u2, st["stake"])
            verdict = "🤝 Ничья, ставки возвращены."
        else:
            w, wn = (u1, n1) if s1 > s2 else (u2, n2)
            reward(chat, w, wn, st["pot"], game="duel")
            verdict = f"🏆 Победил(а) <b>{shown(w, wn)}</b> и забрал(а) <b>{st['pot']}</b> 💰"
        await edit_key(bot, key, f"⚔️ <b>Итоги дуэли</b>\n{LINE}\n{esc(n1)}: {s1}\n{esc(n2)}: {s2}\n\n{verdict}",
                       _kb([("‹ Игры", "gg:menu")]))
        return
    ranked = sorted(scores.items(), key=lambda x: -x[1])
    if not ranked or ranked[0][1] == 0:
        await edit_key(bot, key, f"🧠 <b>Итоги</b>\n{LINE}\nНикто не ответил правильно. Попробуем ещё раз?",
                       _kb([("‹ Игры", "gg:menu")]))
        return
    top = ranked[0][1]
    lines = []
    for n, (u, sc) in enumerate(ranked[:10]):
        if sc == top:
            reward(chat, u, names[u], 100, game="quiz")
        else:
            add_coins(u, 20, names[u])
        lines.append(f"{MEDALS[n] if n < 3 else f'{n + 1}.'} {shown(u, names[u])} — <b>{sc}</b>")
    await edit_key(bot, key, f"🧠 <b>Итоги викторины</b>\n{LINE}\n" + "\n".join(lines) +
                   "\n\n<i>Победитель +100 💰 и очко в лидеры, остальные +20 💰.</i>", _kb([("‹ Игры", "gg:menu")]))


async def gg_quiz(q, ctx, st, action, args):
    user = q.from_user
    if action != "qa" or len(args) < 2:
        await q.answer()
        return
    i, k = int(args[0]), int(args[1])
    if i != st["i"] or st["revealing"]:
        await q.answer("Время на этот вопрос вышло", show_alert=True)
        return
    if st["players"] is not None and user.id not in st["players"]:
        await q.answer("В дуэли участвуют двое", show_alert=True)
        return
    if user.id in st["answers"]:
        await q.answer("Вы уже ответили", show_alert=True)
        return
    st["answers"][user.id] = (k, time_module.monotonic())
    st["names"][user.id] = _name(user)
    await q.answer("Ответ принят ✅")
    if st["kind"] == "duel" and len(st["answers"]) >= 2:
        spawn(quiz_reveal(ctx.bot, (q.message.chat.id, q.message.message_id), i))


async def quiz_start(q, ctx, kind: str):
    if kind == "quiz18" and not adult_ok(q.from_user.id):
        await q.answer("Викторину 18+ может запустить только тот, кому владелец разрешил 18+", show_alert=True)
        return
    await q.answer()
    bank = QUIZ18 if kind == "quiz18" else QUIZ
    st = {"type": "quiz", "kind": kind, "qs": [prep_q(x) for x in random.sample(bank, min(5, len(bank)))],
          "i": -1, "answers": {}, "scores": {}, "names": {}, "players": None, "pot": 0, "stake": 0, "revealing": False}
    tag = "🔞 Викторина 18+" if kind == "quiz18" else "🧠 Викторина"
    m = await q.message.reply_text(f"<b>{tag}</b>\n{LINE}\n5 вопросов, на каждый по {QUIZ_SECONDS} секунд.\n"
                                   "Начинаем через 5 секунд, приготовьтесь!", parse_mode="HTML")
    key = (q.message.chat.id, m.message_id)
    gg_put(key, st)
    spawn(quiz_next(ctx.bot, key, delay=5))


# --- дуэль эрудитов
async def gg_duel(q, ctx, st, action, args):
    user = q.from_user
    if action == "dstake" and st["type"] == "duel_setup":
        if user.id != st["host"]:
            await q.answer("Ставку выбирает тот, кто вызывает", show_alert=True)
            return
        stake = int(args[0]) if args and args[0].isdigit() else 0
        if stake not in (50, 100, 500):
            await q.answer()
            return
        if acct(user.id)["coins"] < stake:
            await q.answer(f"Не хватает монет: у вас {acct(user.id)['coins']}", show_alert=True)
            return
        st.update({"type": "duel_wait", "stake": stake})
        await q.answer()
        await show(q, f"⚔️ <b>Дуэль эрудитов</b>\n{LINE}\n{shown(user.id, _name(user))} ставит <b>{stake}</b> 💰.\n"
                      "Три вопроса, побеждает тот, кто набрал больше. Кто примет вызов?",
                   _kb([(f"⚔️ Принять ({stake} 💰)", "gg:dacc")], [("✖ Отмена", "gg:dcancel")]))
    elif action == "dcancel" and st["type"] == "duel_wait":
        if user.id not in (st["host"], OWNER_ID):
            await q.answer()
            return
        GG.pop((q.message.chat.id, q.message.message_id), None)
        await q.answer()
        await show(q, "Вызов отменён.", _kb([("‹ Игры", "gg:menu")]))
    elif action == "dacc" and st["type"] == "duel_wait":
        if user.id == st["host"]:
            await q.answer("Нужен соперник, а не вы 🙂", show_alert=True)
            return
        stake = st["stake"]
        if acct(user.id)["coins"] < stake or acct(st["host"])["coins"] < stake:
            await q.answer("У одного из игроков не хватает монет", show_alert=True)
            return
        spend(user.id, stake)
        spend(st["host"], stake)
        key = (q.message.chat.id, q.message.message_id)
        host_id, host_name = st["host"], st["host_name"]
        st.clear()
        st.update({"type": "quiz", "kind": "duel", "qs": [prep_q(x) for x in random.sample(QUIZ, 3)], "i": -1,
                   "answers": {}, "scores": {}, "names": {host_id: host_name, user.id: _name(user)},
                   "players": {host_id, user.id}, "p1": (host_id, host_name), "p2": (user.id, _name(user)),
                   "pot": stake * 2, "stake": stake, "revealing": False})
        await q.answer()
        await show(q, f"⚔️ <b>Дуэль началась!</b>\n{LINE}\n{esc(host_name)} против {esc(_name(user))}\n"
                      f"Банк: <b>{stake * 2}</b> 💰. Первый вопрос через 3 секунды…", None)
        spawn(quiz_next(ctx.bot, key, delay=3))


# --- казино
RED = {1, 3, 5, 7, 9, 12, 14, 16, 18, 19, 21, 23, 25, 27, 30, 32, 34, 36}
LAST_SPIN: dict[int, float] = {}


def casino_text(uid: int) -> str:
    return (f"🎰 <b>Казино</b>\n{LINE}\n💰 Ваш баланс: <b>{acct(uid)['coins']}</b>\n\n"
            "<b>Слоты</b>: три семёрки ×10, три одинаковых ×5, пара: ставка возвращается.\n"
            "<b>Рулетка</b>: красное или чёрное ×2, зеро ×36, ставки общие на раунд.\n\n"
            "<i>Играйте на виртуальные монеты и в меру 🙂</i>")


def casino_kb() -> InlineKeyboardMarkup:
    return _kb([(f"🎰 Слоты · {s}", f"gg:slot:{s}") for s in (10, 50)],
               [(f"🎰 Слоты · {s}", f"gg:slot:{s}") for s in (100, 500)],
               [("🎡 Рулетка", "gg:new:roul")], [("‹ Игры", "gg:menu")])


async def slot_spin(q, ctx, stake: int):
    uid = q.from_user.id
    if stake not in (10, 50, 100, 500):
        await q.answer()
        return
    now = time_module.time()
    if now - LAST_SPIN.get(uid, 0) < 6:
        await q.answer("Подождите пару секунд ⏳")
        return
    if not spend(uid, stake):
        await q.answer(f"Не хватает монет: у вас {acct(uid)['coins']}", show_alert=True)
        return
    LAST_SPIN[uid] = now
    await q.answer()
    d = await q.message.reply_dice(emoji="🎰")
    v = d.dice.value - 1
    await asyncio.sleep(2.5)
    a, b, c = v % 4, (v // 4) % 4, v // 16
    if a == b == c:
        mult, text = (10, "Джекпот: три семёрки!") if a == 3 else (5, "Три одинаковых!")
    elif a == b or b == c or a == c:
        mult, text = 1, "Пара: ставка вернулась."
    else:
        mult, text = 0, "Не повезло."
    win = stake * mult
    if win:
        add_coins(uid, win)
    delta = win - stake
    sign = f"+{delta}" if delta > 0 else (f"{delta}" if delta < 0 else "±0")
    await q.message.reply_text(f"🎰 {shown(uid, _name(q.from_user))}: {text}\n<b>{sign}</b> 💰 · баланс {acct(uid)['coins']}",
                               parse_mode="HTML")


def roul_text(st: dict) -> str:
    sym = {"r": "🔴", "b": "⚫", "z": "🟢"}
    lines = "\n".join(f"{sym[b]} {esc(n)}" for n, b in st["bets"].values()) or "Ставок пока нет."
    return (f"🎡 <b>Рулетка</b>  ·  ставка <b>{st['stake']}</b> 💰\n{LINE}\n{lines}\n\n"
            f"<i>Крутим через 45 секунд или когда ведущий ({esc(st['host_name'])}) нажмёт кнопку.</i>")


ROUL_KB = lambda: _kb([("🔴 Красное ×2", "gg:rb:r"), ("⚫ Чёрное ×2", "gg:rb:b")], [("🟢 Зеро ×36", "gg:rb:z")],
                      [("🎡 Крутить", "gg:rspin")])


async def roul_spin(bot, key):
    st = GG.get(key)
    if st is None or st.get("spun"):
        return
    st["spun"] = True
    n = random.randint(0, 36)
    col = "z" if n == 0 else ("r" if n in RED else "b")
    sym = {"r": "🔴 красное", "b": "⚫ чёрное", "z": "🟢 зеро"}[col]
    lines = []
    for uid, (name, bet) in st["bets"].items():
        if bet == col:
            pay = st["stake"] * (36 if col == "z" else 2)
            add_coins(uid, pay)
            lines.append(f"✅ {shown(uid, name)}: +{pay - st['stake']}")
        else:
            lines.append(f"❌ {shown(uid, name)}: −{st['stake']}")
    GG.pop(key, None)
    await edit_key(bot, key, f"🎡 <b>Выпало {n}</b>, {sym}\n{LINE}\n" + ("\n".join(lines) or "Никто не ставил."),
                   _kb([("🎡 Ещё раунд", "gg:new:roul"), ("‹ Игры", "gg:menu")]))


async def roul_timer(bot, key):
    await asyncio.sleep(45)
    await roul_spin(bot, key)


async def gg_roul(q, ctx, st, action, args):
    user = q.from_user
    key = (q.message.chat.id, q.message.message_id)
    if action == "rs" and st["type"] == "roul_setup":
        if user.id != st["host"]:
            await q.answer("Ставку выбирает ведущий", show_alert=True)
            return
        stake = int(args[0]) if args and args[0].isdigit() else 0
        if stake not in (10, 50, 100, 500):
            await q.answer()
            return
        st.update({"type": "roul", "stake": stake, "bets": {}, "spun": False})
        await q.answer()
        await show(q, roul_text(st), ROUL_KB())
        spawn(roul_timer(ctx.bot, key))
    elif action == "rb" and st["type"] == "roul":
        bet = args[0] if args else ""
        if bet not in ("r", "b", "z") or st.get("spun"):
            await q.answer()
            return
        if user.id in st["bets"]:
            await q.answer("Ваша ставка уже сделана", show_alert=True)
            return
        if not spend(user.id, st["stake"]):
            await q.answer(f"Не хватает монет: у вас {acct(user.id)['coins']}", show_alert=True)
            return
        st["bets"][user.id] = (_name(user), bet)
        await q.answer("Ставка принята ✅")
        await show(q, roul_text(st), ROUL_KB())
    elif action == "rspin" and st["type"] == "roul":
        if user.id not in (st["host"], OWNER_ID):
            await q.answer("Крутит ведущий, либо подождите 45 секунд", show_alert=True)
            return
        await q.answer()
        await roul_spin(ctx.bot, key)


# --- создание игр и общий обработчик кнопок группы
async def gg_new(q, ctx, kind: str):
    user, chat = q.from_user, q.message.chat
    name = _name(user)
    if kind in ("quiz", "quiz18"):
        await quiz_start(q, ctx, kind)
        return
    if kind == "mafia":
        await mafia_new(q, ctx)
        return
    if kind == "rps":
        st = {"type": "rps", "p1": (user.id, name), "p2": None, "choices": {}}
        m = await q.message.reply_text(rps_text(st), parse_mode="HTML", reply_markup=_kb([("⚔️ Принять вызов", "gg:join")]))
    elif kind == "who":
        c = cands(chat.id)
        if not any(u == user.id for u, _ in c):
            c.append((user.id, name))
        if len(c) < 3:
            await q.answer("Мне нужно знать хотя бы троих. Пусть остальные нажмут «🙋 Я в компании» в /games",
                           show_alert=True)
            return
        st = {"type": "who", "q": random.choice(WHO), "votes": {}, "cands": c[-12:], "host": user.id, "host_name": name}
        m = await q.message.reply_text(who_text(st), parse_mode="HTML", reply_markup=who_kb(st))
    elif kind == "duel":
        st = {"type": "duel_setup", "host": user.id, "host_name": name}
        m = await q.message.reply_text(
            f"⚔️ <b>Дуэль эрудитов</b>\n{LINE}\n{esc(name)}, выберите ставку:", parse_mode="HTML",
            reply_markup=_kb([("50 💰", "gg:dstake:50"), ("100 💰", "gg:dstake:100"), ("500 💰", "gg:dstake:500")]))
    elif kind == "roul":
        st = {"type": "roul_setup", "host": user.id, "host_name": name}
        m = await q.message.reply_text(
            f"🎡 <b>Рулетка</b>\n{LINE}\n{esc(name)}, выберите ставку на раунд:", parse_mode="HTML",
            reply_markup=_kb([(f"{s} 💰", f"gg:rs:{s}") for s in (10, 50, 100, 500)]))
    else:
        await q.answer()
        return
    await q.answer()
    gg_put((chat.id, m.message_id), st)


STATEFUL = {"rps": gg_rps, "who": gg_who, "quiz": gg_quiz, "duel_setup": gg_duel, "duel_wait": gg_duel,
            "roul_setup": gg_roul, "roul": gg_roul}


async def on_gg(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    chat, user = q.message.chat, q.from_user
    if chat.type == "private" or chat.id not in USERS["groups"] or user.id in USERS["blocked"]:
        await q.answer()
        return
    acct(user.id, _name(user))
    parts = q.data.split(":")[1:]
    action, args = parts[0], parts[1:]
    if action == "menu":
        await q.answer()
        await show(q, GAMES_TITLE, games_kb())
    elif action in ("top", "lb"):
        await q.answer()
        scope = args[0] if action == "lb" and args and args[0] in ("g", "a") else "g"
        mode = (args[1] if action == "lb" and len(args) > 1 else args[0] if args else "w")
        mode = mode if mode in LB_MODES else "w"
        await show(q, lb_text(mode, chat.id if scope == "g" else None), lb_kb(f"gg:lb:{scope}:", mode, scope))
    elif action == "here":
        await q.answer("Записал вас в компанию ✅")
    elif action == "new":
        await gg_new(q, context, args[0] if args else "")
    elif action == "casino":
        await q.answer()
        await show(q, casino_text(user.id), casino_kb())
    elif action == "slot":
        await slot_spin(q, context, int(args[0]) if args and args[0].isdigit() else 0)
    elif action in ("mj", "ms", "mx", "mv"):
        await mafia_action(q, context, action, args)
    elif action == "askmenu":
        await ask_menu(q, context)
    elif action in ("askto", "ag", "ar", "ax"):
        await ask_action(q, context, action, args)
    else:
        st = GG.get((chat.id, q.message.message_id))
        if st is None:
            await q.answer("Эта игра закончена или бот перезапускался. Откройте /games", show_alert=True)
            return
        handler = STATEFUL.get(st["type"])
        if handler is None:
            await q.answer()
            return
        await handler(q, context, st, action, args)


async def on_bot_added(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Бота добавили в группу или убрали из неё."""
    cmu = update.my_chat_member
    chat = cmu.chat
    if chat.type == "private":
        return
    status = cmu.new_chat_member.status
    if status in ("left", "kicked"):
        if USERS["groups"].pop(chat.id, None) is not None:
            _save_users()
        return
    if status not in ("member", "administrator") or chat.id in USERS["groups"]:
        return
    adder, title = cmu.from_user, chat.title or f"чат {chat.id}"
    if is_allowed(adder.id):                                 # добавил владелец или друг: сразу разрешаем
        USERS["groups"][chat.id] = title
        _save_users()
        await context.bot.send_message(chat.id, GROUP_HELLO, parse_mode="HTML", reply_markup=games_kb())
        return
    GROUP_PENDING[chat.id] = f"{title} (добавил(а): {adder.full_name})"
    try:
        await context.bot.send_message(
            OWNER_ID, f"🔔 Бота добавили в группу\n{GROUP_PENDING[chat.id]}\nID чата: {chat.id}",
            reply_markup=_kb([("✅ Разрешить", f"acc:gok:{chat.id}"), ("🚪 Выйти", f"acc:gno:{chat.id}")]))
        await context.bot.send_message(chat.id, "⏳ Жду разрешения владельца бота.")
    except Exception:
        log.exception("не удалось спросить разрешение для группы")



# ====================== мафия ======================
MAF: dict[int, dict] = {}                         # чат -> состояние игры
ROLE_NAME = {"mafia": "🔫 Мафия", "doctor": "💉 Доктор", "sheriff": "🕵️ Комиссар", "civ": "🧑 Мирный житель"}
ROLE_HINT = {
    "mafia": "Ночью вместе с мафией выбираете жертву. Днём изображайте мирного жителя.",
    "doctor": "Каждую ночь выбираете, кого вылечить. Если мафия выберет его, он выживет.",
    "sheriff": "Каждую ночь проверяете одного игрока: узнаете, мафия ли он.",
    "civ": "Ночью вы спите. Днём ищите мафию и голосуйте.",
}
NIGHT_SECONDS, DAY_SECONDS = 60, 90


def maf_roles(n: int) -> list[str]:
    mafia = max(1, n // 3)
    special = ["doctor"] if n == 4 else ["doctor", "sheriff"]
    roles = ["mafia"] * mafia + special + ["civ"] * (n - mafia - len(special))
    random.shuffle(roles)
    return roles


def maf_lobby_text(st: dict) -> str:
    names = "\n".join(f"• {shown(u, n)}" for u, n in st["players"].items())
    return (f"🕵️ <b>Мафия</b>  ·  набор игроков\n{LINE}\n{names}\n\n"
            f"Игроков: <b>{len(st['players'])}</b> (нужно 4–10). Ведущий: {esc(st['host_name'])}.\n"
            "<i>Вступайте кнопкой. Я пришлю роль в личные сообщения, поэтому сначала откройте меня в личке и "
            "нажмите «Запустить».</i>")


def maf_lobby_kb(bot_username: str) -> InlineKeyboardMarkup:
    return _kb([("➕ Вступить", "gg:mj"), ("▶️ Начать", "gg:ms")],
               [("🔗 Открыть бота в личке", "url", f"https://t.me/{bot_username}?start=g")],
               [("✖ Отменить набор", "gg:mx")])


async def mafia_new(q, ctx):
    chat = q.message.chat.id
    if chat in MAF:
        await q.answer("В этой группе уже идёт игра или набор", show_alert=True)
        return
    user = q.from_user
    st = {"host": user.id, "host_name": _name(user), "players": {}, "phase": "lobby", "roles": {}, "alive": set(),
          "night": {}, "need": set(), "votes": {}, "round": 0, "msg": None}
    MAF[chat] = st
    await q.answer()
    m = await q.message.reply_text(maf_lobby_text(st), parse_mode="HTML",
                                   reply_markup=maf_lobby_kb(ctx.bot.username or ""))
    st["msg"] = m.message_id


async def mafia_action(q, ctx, action, args):
    chat, user = q.message.chat.id, q.from_user
    st = MAF.get(chat)
    if st is None:
        await q.answer("Игра не найдена. Начните новую в /games", show_alert=True)
        return
    if action == "mj":
        if st["phase"] != "lobby":
            await q.answer("Набор закончен", show_alert=True)
            return
        if user.id in st["players"]:
            await q.answer("Вы уже в игре")
            return
        if len(st["players"]) >= 10:
            await q.answer("Мест нет: максимум 10 игроков", show_alert=True)
            return
        try:
            await ctx.bot.send_message(user.id, "✅ Вы в игре «Мафия». Роль придёт сюда, когда ведущий начнёт игру.")
        except Exception:
            await q.answer("Сначала откройте меня в личке и нажмите «Запустить» (кнопка под сообщением), "
                           "потом вступите снова.", show_alert=True)
            return
        st["players"][user.id] = _name(user)
        await q.answer("Вы в игре ✅")
        await show(q, maf_lobby_text(st), maf_lobby_kb(ctx.bot.username or ""))
    elif action == "mx":
        if user.id not in (st["host"], OWNER_ID):
            await q.answer("Отменяет ведущий", show_alert=True)
            return
        MAF.pop(chat, None)
        await q.answer()
        await show(q, "🕵️ Игра отменена.", _kb([("‹ Игры", "gg:menu")]))
    elif action == "ms":
        if user.id not in (st["host"], OWNER_ID):
            await q.answer("Начинает ведущий", show_alert=True)
            return
        if st["phase"] != "lobby":
            await q.answer()
            return
        n = len(st["players"])
        if n < 4:
            await q.answer("Нужно минимум 4 игрока", show_alert=True)
            return
        st["phase"] = "night"                          # сразу занимаем фазу, чтобы не запустили дважды
        await q.answer()
        ids = list(st["players"])
        roles = maf_roles(n)
        st["roles"] = dict(zip(ids, roles))
        st["alive"] = set(ids)
        team = [st["players"][u] for u in ids if st["roles"][u] == "mafia"]
        failed = []
        for u in ids:
            r = st["roles"][u]
            text = f"🎭 <b>Ваша роль: {ROLE_NAME[r]}</b>\n{LINE}\n{ROLE_HINT[r]}"
            if r == "mafia" and len(team) > 1:
                text += f"\n\nВаша команда: {', '.join(esc(x) for x in team)}"
            try:
                await ctx.bot.send_message(u, text, parse_mode="HTML")
            except Exception:
                failed.append(st["players"][u])
        if failed:
            MAF.pop(chat, None)
            await show(q, "⚠️ Не смог написать: " + ", ".join(esc(x) for x in failed) +
                       ". Пусть откроют меня в личке и нажмут «Запустить», затем начните заново.",
                       _kb([("‹ Игры", "gg:menu")]))
            return
        mafia_n = sum(1 for r in roles if r == "mafia")
        await show(q, f"🕵️ <b>Мафия</b>\n{LINE}\nИгра началась! Игроков: {n}, мафии: {mafia_n}.\n"
                      "Роли разосланы в личные сообщения.", None)
        await maf_night(ctx.bot, chat)
    elif action == "mv":
        await maf_vote(q, ctx, st, args)


def maf_alive_names(st: dict, exclude=()) -> list[tuple[int, str]]:
    return [(u, st["players"][u]) for u in st["players"] if u in st["alive"] and u not in exclude]


async def maf_night(bot, chat: int):
    st = MAF.get(chat)
    if st is None:
        return
    st["round"] += 1
    st["phase"], st["night"], st["votes"] = "night", {}, {}
    rnd = st["round"]
    alive = st["alive"]
    mafia = [u for u in alive if st["roles"][u] == "mafia"]
    doctor = [u for u in alive if st["roles"][u] == "doctor"]
    sheriff = [u for u in alive if st["roles"][u] == "sheriff"]
    st["need"] = set(mafia) | set(doctor) | set(sheriff)
    await bot.send_message(chat, f"🌙 <b>Ночь {rnd}</b>\n{LINE}\nГород засыпает. Мафия, доктор и комиссар, "
                                 f"проверьте личные сообщения. У вас {NIGHT_SECONDS} секунд.", parse_mode="HTML")
    for act, group, title in (("k", mafia, "🔫 Кого убрать этой ночью?"), ("h", doctor, "💉 Кого вылечить?"),
                              ("c", sheriff, "🕵️ Кого проверить?")):
        for u in group:
            targets = maf_alive_names(st, exclude=(u,) if act in ("k", "c") else ())
            if act == "k":
                targets = [t for t in targets if st["roles"][t[0]] != "mafia"]
            rows = [[(n, f"mf:{chat}:{act}:{t}")] for t, n in targets]
            try:
                await bot.send_message(u, f"🌙 <b>Ночь {rnd}</b>\n{title}", parse_mode="HTML", reply_markup=_kb(*rows))
            except Exception:
                log.exception("не удалось отправить ночное действие")
    spawn(maf_timer(bot, chat, "night", rnd, NIGHT_SECONDS))


async def maf_timer(bot, chat, phase, rnd, secs):
    await asyncio.sleep(secs)
    if phase == "night":
        await maf_resolve_night(bot, chat, rnd)
    else:
        await maf_resolve_day(bot, chat, rnd)


async def on_mf(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Ночные действия мафии, доктора и комиссара: кнопки в личных сообщениях."""
    q = update.callback_query
    user = q.from_user
    if q.message.chat.type != "private":
        await q.answer()
        return
    try:
        _, chat_s, act, target_s = q.data.split(":")
        chat, target = int(chat_s), int(target_s)
    except ValueError:
        await q.answer()
        return
    st = MAF.get(chat)
    role = {"k": "mafia", "h": "doctor", "c": "sheriff"}.get(act)
    if (st is None or st["phase"] != "night" or user.id not in st["alive"] or st["roles"].get(user.id) != role
            or target not in st["alive"]):
        await q.answer("Это действие сейчас недоступно", show_alert=True)
        return
    if user.id in st["night"]:
        await q.answer("Вы уже выбрали", show_alert=True)
        return
    st["night"][user.id] = target
    name = st["players"][target]
    if act == "c":
        is_mafia = st["roles"][target] == "mafia"
        await q.answer()
        await show(q, f"🕵️ {esc(name)}: <b>{'мафия 🔫' if is_mafia else 'не мафия ✅'}</b>")
    else:
        await q.answer("Выбор принят")
        await show(q, f"✅ Выбор принят: {esc(name)}")
    if st["need"] <= set(st["night"]):
        spawn(maf_resolve_night(context.bot, chat, st["round"]))


def maf_win(st: dict):
    mafia = [u for u in st["alive"] if st["roles"][u] == "mafia"]
    others = [u for u in st["alive"] if st["roles"][u] != "mafia"]
    if not mafia:
        return "civ"
    if len(mafia) >= len(others):
        return "mafia"
    return None


async def maf_end(bot, chat: int, winner: str):
    st = MAF.pop(chat, None)
    if st is None:
        return
    lines, win_team = [], []
    for u, name in st["players"].items():
        r = st["roles"][u]
        mine = (r == "mafia") == (winner == "mafia")
        if mine:
            reward(chat, u, name, 150, game="mafia")
            win_team.append(name)
        else:
            add_coins(u, 30, name)
        lines.append(f"{'🏆' if mine else '•'} {shown(u, name)}: {ROLE_NAME[r]}")
    title = "🔫 Победила мафия!" if winner == "mafia" else "🏙 Победил город!"
    await bot.send_message(chat, f"🕵️ <b>{title}</b>\n{LINE}\n" + "\n".join(lines) +
                           "\n\n<i>Победители +150 💰 и очко в лидеры, остальные +30 💰.</i>",
                           parse_mode="HTML", reply_markup=_kb([("‹ Игры", "gg:menu")]))


async def maf_resolve_night(bot, chat: int, rnd: int):
    st = MAF.get(chat)
    if st is None or st["phase"] != "night" or st["round"] != rnd:
        return
    st["phase"] = "resolving"
    kills = [t for u, t in st["night"].items() if st["roles"][u] == "mafia"]
    heal = next((t for u, t in st["night"].items() if st["roles"][u] == "doctor"), None)
    victim = None
    if kills:
        counts = defaultdict(int)
        for t in kills:
            counts[t] += 1
        top = max(counts.values())
        victim = random.choice([t for t, c in counts.items() if c == top])
    if victim is not None and victim != heal:
        st["alive"].discard(victim)
        text = (f"☀️ <b>Наступило утро</b>\n{LINE}\nЭтой ночью убит(а) <b>{esc(st['players'][victim])}</b> "
                f"({ROLE_NAME[st['roles'][victim]]}).")
    else:
        text = f"☀️ <b>Наступило утро</b>\n{LINE}\nЭтой ночью никто не погиб."
    await bot.send_message(chat, text, parse_mode="HTML")
    win = maf_win(st)
    if win:
        await maf_end(bot, chat, win)
        return
    await maf_day(bot, chat)


def maf_vote_kb(st: dict) -> InlineKeyboardMarkup:
    btns = [(n[:16], f"gg:mv:{u}") for u, n in maf_alive_names(st)]
    return _kb(*[btns[i:i + 2] for i in range(0, len(btns), 2)])


async def maf_day(bot, chat: int):
    st = MAF.get(chat)
    if st is None:
        return
    st["phase"], st["votes"] = "day", {}
    rnd = st["round"]
    alive = ", ".join(esc(n) for _, n in maf_alive_names(st))
    await bot.send_message(chat, f"🗣 <b>День {rnd}</b>\n{LINE}\nЖивы: {alive}\n\n"
                                 f"Обсудите и проголосуйте, кого казнить. У вас {DAY_SECONDS} секунд.",
                           parse_mode="HTML", reply_markup=maf_vote_kb(st))
    spawn(maf_timer(bot, chat, "day", rnd, DAY_SECONDS))


async def maf_vote(q, ctx, st, args):
    user = q.from_user
    if st["phase"] != "day" or user.id not in st["alive"]:
        await q.answer("Голосуют только живые игроки днём", show_alert=True)
        return
    if not args or not args[0].lstrip("-").isdigit() or int(args[0]) not in st["alive"]:
        await q.answer()
        return
    target = int(args[0])
    st["votes"][user.id] = target
    await q.answer(f"Голос за {st['players'][target]} принят")
    if set(st["votes"]) >= st["alive"]:
        spawn(maf_resolve_day(ctx.bot, q.message.chat.id, st["round"]))


async def maf_resolve_day(bot, chat: int, rnd: int):
    st = MAF.get(chat)
    if st is None or st["phase"] != "day" or st["round"] != rnd:
        return
    st["phase"] = "resolving"
    counts = defaultdict(int)
    for t in st["votes"].values():
        counts[t] += 1
    top = max(counts.values()) if counts else 0
    leaders = [t for t, c in counts.items() if c == top]
    if top and len(leaders) == 1:
        v = leaders[0]
        st["alive"].discard(v)
        text = (f"⚖️ <b>Итоги голосования</b>\n{LINE}\nГород казнил <b>{esc(st['players'][v])}</b> "
                f"({ROLE_NAME[st['roles'][v]]}).")
    else:
        text = f"⚖️ <b>Итоги голосования</b>\n{LINE}\nМнения разделились, никого не казнили."
    await bot.send_message(chat, text, parse_mode="HTML")
    win = maf_win(st)
    if win:
        await maf_end(bot, chat, win)
        return
    await maf_night(bot, chat)



# ====================== анонимные вопросы ======================
AQ: dict[int, dict] = {}
AQ_COUNTER = [0]
AQ_RATE: dict[int, list[float]] = defaultdict(list)
AQ_MAX_PER_HOUR = 5


def mention(uid: int, name: str) -> str:
    return f'<a href="tg://user?id={uid}">{esc(name)}</a>'


def ask_link_kb(bot_username: str, chat: int, target: int) -> InlineKeyboardMarkup:
    return _kb([("✍️ Написать вопрос", "url", f"https://t.me/{bot_username}?start=ask_{chat}_{target}")],
               [("‹ Игры", "gg:menu")])


async def ask_menu(q, ctx):
    chat = q.message.chat.id
    c = cands(chat, exclude=(q.from_user.id,))
    if not c:
        await q.answer("Я пока не знаю, кому задать вопрос. Пусть другие нажмут «🙋 Я в компании» или ответьте "
                       "командой /ask на чьё-то сообщение", show_alert=True)
        return
    await q.answer()
    btns = [(n[:14], f"gg:askto:{u}") for u, n in c]
    rows = [btns[i:i + 2] for i in range(0, len(btns), 2)] + [[("‹ Игры", "gg:menu")]]
    await show(q, f"💌 <b>Анонимный вопрос</b>\n{LINE}\nКому хотите задать вопрос?", _kb(*rows))


async def ask_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg, chat = update.effective_message, update.effective_chat
    r = msg.reply_to_message
    if r and r.from_user and not r.from_user.is_bot:
        see(chat.id, r.from_user)
        await msg.reply_text(
            f"💌 <b>Анонимный вопрос</b> для {mention(r.from_user.id, _name(r.from_user))}\n{LINE}\n"
            "Нажмите кнопку: откроется личка со мной, там напишите вопрос. Ваше имя останется скрытым.",
            parse_mode="HTML", reply_markup=ask_link_kb(context.bot.username or "", chat.id, r.from_user.id))
        return
    c = cands(chat.id, exclude=(update.effective_user.id,))
    if not c:
        await msg.reply_text("Ответьте командой /ask на сообщение человека, которому хотите задать вопрос.")
        return
    btns = [(n[:14], f"gg:askto:{u}") for u, n in c]
    rows = [btns[i:i + 2] for i in range(0, len(btns), 2)]
    await msg.reply_text(f"💌 <b>Анонимный вопрос</b>\n{LINE}\nКому хотите задать вопрос?", parse_mode="HTML",
                         reply_markup=_kb(*rows))


async def ask_begin(update: Update, context: ContextTypes.DEFAULT_TYPE, payload: str):
    """Человек открыл личку по ссылке «Написать вопрос»."""
    msg, user = update.message, update.effective_user
    try:
        _, chat_s, target_s = payload.split("_")
        chat, target = int(chat_s), int(target_s)
    except ValueError:
        await msg.reply_text("Эта ссылка не работает. Откройте её заново из группы.")
        return
    if chat not in USERS["groups"] or user.id in USERS["blocked"] or target == user.id:
        await msg.reply_text("Сюда вопрос отправить нельзя.")
        return
    try:
        member = await context.bot.get_chat_member(chat, user.id)
        if member.status in ("left", "kicked"):
            raise ValueError
        tm = await context.bot.get_chat_member(chat, target)
        target_name = _name(tm.user)
    except Exception:
        await msg.reply_text("Вы не состоите в этой группе, поэтому задать вопрос не получится.")
        return
    now = time_module.time()
    AQ_RATE[user.id] = [t for t in AQ_RATE[user.id] if now - t < 3600]
    if len(AQ_RATE[user.id]) >= AQ_MAX_PER_HOUR:
        await msg.reply_text(f"Не больше {AQ_MAX_PER_HOUR} анонимных вопросов в час. Попробуйте позже.")
        return
    context.user_data["ask"] = {"chat": chat, "target": target, "name": target_name}
    await msg.reply_text(f"💌 Напишите вопрос для <b>{esc(target_name)}</b> (до 300 символов).\n"
                         "Он появится в группе без вашего имени.", parse_mode="HTML")


async def ask_submit(update: Update, context: ContextTypes.DEFAULT_TYPE, text: str):
    msg, user = update.message, update.effective_user
    data = context.user_data.get("ask")
    if not data:
        return
    text = text.strip()
    if not text or len(text) > 300:
        await msg.reply_text("Вопрос должен быть не длиннее 300 символов. Напишите ещё раз.")
        return
    chat, target = data["chat"], data["target"]
    if chat not in USERS["groups"] or user.id in USERS["blocked"]:
        context.user_data.pop("ask", None)
        return
    now = time_module.time()
    AQ_RATE[user.id] = [t for t in AQ_RATE[user.id] if now - t < 3600]
    if len(AQ_RATE[user.id]) >= AQ_MAX_PER_HOUR:
        context.user_data.pop("ask", None)
        await msg.reply_text("Лимит вопросов в час исчерпан.")
        return
    context.user_data.pop("ask", None)
    AQ_RATE[user.id].append(now)
    AQ_COUNTER[0] += 1
    qid = AQ_COUNTER[0]
    c = cands(chat, exclude=(target,))
    if not any(u == user.id for u, _ in c):
        c.append((user.id, _name(user)))
    AQ[qid] = {"chat": chat, "author": user.id, "author_name": _name(user), "target": target,
               "target_name": data["name"], "text": text, "guesses": {}, "done": False}
    if len(AQ) > 200:
        AQ.pop(next(iter(AQ)))
    try:
        sent = await context.bot.send_message(chat, ask_post_text(AQ[qid]), parse_mode="HTML",
                                              reply_markup=ask_post_kb(qid, c))
    except Exception:
        log.exception("не удалось отправить анонимный вопрос в группу")
        await msg.reply_text("Не получилось отправить вопрос в группу.")
        return
    AQ[qid]["msg"] = sent.message_id
    await msg.reply_text("✅ Вопрос отправлен анонимно.")


def ask_post_text(a: dict) -> str:
    return (f"💌 <b>Анонимный вопрос</b> для {mention(a['target'], a['target_name'])}\n{LINE}\n«{esc(a['text'])}»\n\n"
            f"<i>Угадайте автора кнопками. Угадавшие: {len(a['guesses'])}. Автора раскроет адресат.</i>")


def ask_post_kb(qid: int, c: list[tuple[int, str]]) -> InlineKeyboardMarkup:
    btns = [(f"🕵️ {n[:10]}", f"gg:ag:{qid}:{u}") for u, n in c]
    rows = [btns[i:i + 3] for i in range(0, len(btns), 3)]
    rows.append([("🔓 Раскрыть автора", f"gg:ar:{qid}"), ("🚩 Пожаловаться", f"gg:ax:{qid}")])
    return _kb(*rows)


async def ask_action(q, ctx, action, args):
    user = q.from_user
    if action == "askto":
        if not args or not args[0].lstrip("-").isdigit():
            await q.answer()
            return
        target = int(args[0])
        names = dict(cands(q.message.chat.id))
        await q.answer()
        await show(q, f"💌 <b>Анонимный вопрос</b> для {mention(target, names.get(target, 'участника'))}\n{LINE}\n"
                      "Нажмите кнопку: откроется личка со мной, там напишите вопрос. Ваше имя останется скрытым.",
                   ask_link_kb(ctx.bot.username or "", q.message.chat.id, target))
        return
    qid = int(args[0]) if args and args[0].isdigit() else 0
    a = AQ.get(qid)
    if a is None or a["chat"] != q.message.chat.id:
        await q.answer("Этот вопрос уже закрыт или бот перезапускался", show_alert=True)
        return
    if action == "ag":
        if a["done"]:
            await q.answer("Автор уже раскрыт")
            return
        guess = int(args[1]) if len(args) > 1 and args[1].lstrip("-").isdigit() else 0
        if user.id == a["target"]:
            await q.answer("Вы адресат: вы раскрываете автора кнопкой «Раскрыть»", show_alert=True)
        elif user.id == a["author"]:
            await q.answer("Вы же автор 🙂", show_alert=True)
        elif user.id in a["guesses"]:
            await q.answer("Вы уже сделали догадку", show_alert=True)
        else:
            a["guesses"][user.id] = guess
            await q.answer("Догадка принята 🕵️")
            await show(q, ask_post_text(a), q.message.reply_markup)
    elif action == "ar":
        if user.id not in (a["target"], OWNER_ID) or a["done"]:
            await q.answer("Раскрыть автора может только адресат", show_alert=True)
            return
        a["done"] = True
        await q.answer()
        right = [u for u, g in a["guesses"].items() if g == a["author"]]
        for u in right:
            add_coins(u, 40)
        if not right:
            add_coins(a["author"], 20)
        names = dict(cands(a["chat"]))
        who = ", ".join(shown(u, names.get(u)) for u in right) or "никто"
        await show(q, f"💌 <b>Анонимный вопрос</b> для {mention(a['target'], a['target_name'])}\n{LINE}\n"
                      f"«{esc(a['text'])}»\n\n🔓 Автор: <b>{esc(a['author_name'])}</b>\nУгадали: {who} (+40 💰)"
                      + ("\nНикто не угадал: автору +20 💰" if not right else ""), _kb([("‹ Игры", "gg:menu")]))
    elif action == "ax":
        if user.id != a["target"] or a["done"]:
            await q.answer("Пожаловаться может только адресат", show_alert=True)
            return
        a["done"] = True
        await q.answer("Жалоба отправлена владельцу бота", show_alert=True)
        try:
            await ctx.bot.send_message(
                OWNER_ID, f"🚩 Жалоба на анонимный вопрос\nГруппа: {USERS['groups'].get(a['chat'], a['chat'])}\n"
                          f"Автор: {a['author_name']} (ID {a['author']})\nТекст: {a['text']}",
                reply_markup=_kb([("🚫 Заблокировать автора", f"acc:ban:{a['author']}")]))
        except Exception:
            log.exception("жалоба не дошла до владельца")
        await show(q, "🚩 Вопрос скрыт: по нему отправлена жалоба владельцу бота.", _kb([("‹ Игры", "gg:menu")]))



# ====================== запуск ======================
async def post_init(app: Application):
    """Команды в меню «/», описание и подпись бота."""
    global APP_BOT
    APP_BOT = app.bot
    user_cmds = [BotCommand("start", "🏠 Меню"), BotCommand("weather", "🌦 Погода"), BotCommand("morning", "☀️ Сводка"),
                 BotCommand("rain", "☔ Дождь вкл/выкл"), BotCommand("qr", "🔲 Сделать QR-код"),
                 BotCommand("top", "🏆 Рейтинг")]
    owner_cmds = user_cmds + [BotCommand("friends", "👥 Друзья и группы"), BotCommand("add", "➕ Добавить друга по ID"),
                                  BotCommand("panel", "📊 Панель владельца"), BotCommand("backup", "🗂 Копия данных"),
                                  BotCommand("update", "🔄 Обновить yt-dlp")]
    group_cmds = [BotCommand("games", "🎮 Игры для компании"), BotCommand("top", "🏆 Рейтинг"),
                  BotCommand("ask", "💌 Анонимный вопрос"), BotCommand("gift", "🎁 Подарить монеты")]
    try:
        await app.bot.set_my_commands(user_cmds)
        await app.bot.set_my_commands(owner_cmds, scope=BotCommandScopeChat(OWNER_ID))
        await app.bot.set_my_commands(group_cmds, scope=BotCommandScopeAllGroupChats())
        await app.bot.set_my_short_description("Видео, погода, игры, мафия и многое другое ✨")
        await app.bot.set_my_description(
            "Видео из TikTok, Reels и YouTube, конвертер, QR-коды, погода, утренняя карточка дня, монеты, "
            "магазин, а в группах игры, казино, мафия и анонимные вопросы. Нажмите «Начать» ✨")
    except Exception:
        log.exception("не удалось настроить команды бота")


def main():
    builder = (Application.builder().token(BOT_TOKEN)
               .post_init(post_init)
               .concurrent_updates(True)             # долгая загрузка не блокирует остальные команды
               .read_timeout(1800).write_timeout(1800).connect_timeout(60))
    if LOCAL_API_URL:
        builder = (builder.base_url(f"{LOCAL_API_URL}/bot")
                   .base_file_url(f"{LOCAL_API_URL}/file/bot")
                   .local_mode(True))
    app = builder.build()
    app.add_handler(TypeHandler(Update, guard), group=-1)   # проверка доступа и лимитов первой
    owner = filters.User(OWNER_ID) & filters.ChatType.PRIVATE
    private = filters.ChatType.PRIVATE                       # личные сообщения (доступ проверил guard)
    groups = filters.ChatType.GROUPS
    app.add_handler(CommandHandler("start", start, private))
    app.add_handler(CommandHandler(["help", "menu"], menu_cmd, private))
    app.add_handler(CommandHandler("morning", morning_cmd, private))
    app.add_handler(CommandHandler("weather", weather_cmd, private))
    app.add_handler(CommandHandler("qr", qr_cmd, private))
    app.add_handler(CommandHandler("rain", rain_cmd, private))
    app.add_handler(CommandHandler("top", top_private, private))
    app.add_handler(CommandHandler("friends", friends_cmd, owner))
    app.add_handler(CommandHandler("add", add_cmd, owner))
    app.add_handler(CommandHandler("panel", panel_cmd, owner))
    app.add_handler(CommandHandler("backup", backup_cmd, owner))
    app.add_handler(CommandHandler("update", update_cmd, owner))
    app.add_handler(CommandHandler("gift", gift_cmd, groups))
    app.add_handler(InlineQueryHandler(on_inline))
    app.add_handler(CommandHandler("games", games_cmd, groups))
    app.add_handler(CommandHandler("top", top_group_cmd, groups))
    app.add_handler(CommandHandler("ask", ask_cmd, groups))
    app.add_handler(CommandHandler(["start", "help"], group_help, groups))
    app.add_handler(ChatMemberHandler(on_bot_added, ChatMemberHandler.MY_CHAT_MEMBER))
    app.add_handler(MessageHandler(private & filters.TEXT & ~filters.COMMAND, on_text))
    app.add_handler(MessageHandler(private & (filters.VIDEO | filters.PHOTO | filters.Document.ALL), on_media))
    app.add_handler(CallbackQueryHandler(on_access, pattern=r"^acc:"))
    app.add_handler(CallbackQueryHandler(on_menu, pattern=r"^m:"))
    app.add_handler(CallbackQueryHandler(on_econ, pattern=r"^e:"))
    app.add_handler(CallbackQueryHandler(on_duel, pattern=r"^d:"))
    app.add_handler(CallbackQueryHandler(on_panel, pattern=r"^p:"))
    app.add_handler(CallbackQueryHandler(on_cq, pattern=r"^cq:"))
    app.add_handler(CallbackQueryHandler(on_game, pattern=r"^game:"))
    app.add_handler(CallbackQueryHandler(on_gg, pattern=r"^gg:"))
    app.add_handler(CallbackQueryHandler(on_mf, pattern=r"^mf:"))
    app.add_handler(CallbackQueryHandler(on_button, pattern=r"^(yt|conv):"))
    app.add_error_handler(on_error)
    app.job_queue.run_repeating(morning_tick, interval=300, first=20)   # у каждого своё время и часовой пояс
    app.job_queue.run_daily(period_job, time(0, 10, tzinfo=TZ))        # призы за неделю и месяц, чистка подарков
    app.job_queue.run_daily(backup_job, time(4, 0, tzinfo=TZ), days=(0,))   # копия данных по воскресеньям
    app.job_queue.run_daily(ytdlp_job, time(5, 0, tzinfo=TZ))          # ежедневное обновление yt-dlp
    app.job_queue.run_once(ytdlp_job, 15)                              # и при каждом запуске
    app.job_queue.run_repeating(flush_metrics, interval=120, first=60)
    app.job_queue.run_repeating(check_rain, interval=600, first=30)   # проверка дождя каждые 10 минут
    app.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()
