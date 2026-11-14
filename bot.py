"""Telegram-бот: видео, конвертер, QR, погода, утренняя карточка, правда или действие в личке; игры, казино, мафия и анонимные вопросы в группах."""
import asyncio
import html
import io
import json
import logging
import math
import os
import random
import re
import shutil
import tempfile
import time as time_module
from collections import defaultdict
from datetime import datetime, time, timedelta
from pathlib import Path
from urllib.parse import urlparse
from zoneinfo import ZoneInfo

import feedparser
import httpx
import qrcode
import yt_dlp
from dotenv import load_dotenv
from PIL import Image, ImageOps
from telegram import (BotCommand, BotCommandScopeAllGroupChats, BotCommandScopeChat, InlineKeyboardButton,
                      InlineKeyboardMarkup, ReplyKeyboardMarkup, Update)
from telegram.ext import (
    Application, ApplicationHandlerStop, CallbackQueryHandler, ChatMemberHandler, CommandHandler,
    ContextTypes, MessageHandler, TypeHandler, filters,
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


def city_of(uid: int) -> str:
    return CITY if uid == OWNER_ID else FRIEND_CITY


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
        await context.bot.send_message(OWNER_ID, f"🔔 Заявка на доступ к боту\nИмя: {name}\nID: {uid}",
                                       reply_markup=kb)
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
    if text.startswith("/start g") or text.startswith("/start ask_"):
        return True
    return bool(context.user_data.get("ask")) and not text.startswith("/")


async def guard(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Срабатывает первым на любое обновление: пропускает только своих и режет флуд."""
    user = update.effective_user
    chat = update.effective_chat
    if user is None:
        raise ApplicationHandlerStop
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
        opts["format"] = "bv*[height<=720][ext=mp4]+ba[ext=m4a]/b[height<=720]/b"
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


async def send_media(update: Update, path: str, audio: bool):
    files = [path]
    if os.path.getsize(path) > MAX_UPLOAD:
        await update.effective_message.reply_text("Файл большой, отправлю частями.")
        files = await split_file(path)
    for i, part in enumerate(files, 1):
        caption = f"Часть {i}/{len(files)}" if len(files) > 1 else None
        with open(part, "rb") as f:
            if audio:
                await update.effective_message.reply_audio(f, caption=caption)
            else:
                await update.effective_message.reply_video(f, caption=caption, supports_streaming=True)


async def download_and_send(update: Update, url: str, audio: bool = False):
    uid = update.effective_user.id
    if not url_allowed(url, uid):
        await update.effective_message.reply_text("Поддерживаются ссылки YouTube, TikTok и Instagram.")
        return
    if not await start_job(update):
        return
    tmp = tempfile.mkdtemp()
    msg = None
    try:
        msg = await update.effective_message.reply_text(
            "⏳ В очереди, скоро начну…" if HEAVY.locked() else "🔎 Проверяю ссылку…")
        async with HEAVY:
            await _safe_edit(msg, "⬇️ Скачиваю…")
            path = await asyncio.to_thread(_download, url, audio, tmp, not is_owner(uid))
            await _safe_edit(msg, "📤 Отправляю…")
            await send_media(update, path, audio)
        await msg.delete()
    except Exception as e:
        log.exception("download failed")
        if msg:
            await msg.edit_text(f"❌ Не получилось: {str(e)[:300]}")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
        end_job(update)


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
        async with HEAVY:
            await tg_file.download_to_drive(src)
            await _safe_edit(msg, "⚙️ Обрабатываю…")
            await _convert_work(update, tmp, src, mode)
        await msg.delete()
    except Exception as e:
        log.exception("convert failed")
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


# ====================== экономика: монеты, бонусы, магазин ======================
ECON_FILE = DATA_DIR / "econ.json"
START_COINS = 500


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
                         "chal_day": "", "chal_streak": 0, "items": [], "title": "", "frame": "", "wins": 0}
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


def reward(chat_id: int, uid: int, name: str, coins: int, win: bool = True):
    """Награда игроку: монеты и (если победа) запись в таблицу лидеров группы."""
    if win:
        add_group_win(chat_id, uid, name)
        acct(uid, name)["wins"] += 1
    add_coins(uid, coins, name)


def claim_bonus(uid: int, name=None) -> tuple[bool, int, int]:
    a = acct(uid, name)
    d = today().isoformat()
    if a["last_bonus"] == d:
        return False, 0, a["streak"]
    yest = (today() - timedelta(days=1)).isoformat()
    a["streak"] = a["streak"] + 1 if a["last_bonus"] == yest else 1
    amount = 100 + 20 * (min(a["streak"], 10) - 1)
    a["last_bonus"] = d
    a["coins"] += amount
    _save_econ()
    return True, amount, a["streak"]


CHALLENGES = [
    "Сделайте 15 приседаний прямо сейчас.", "Выпейте стакан воды и позвоните близкому человеку.",
    "Отправьте другу тёплое сообщение без повода.", "Выйдите на 15-минутную прогулку без телефона.",
    "Сделайте зарядку на 5 минут.", "Приготовьте что-нибудь новое на ужин.",
    "Разберите один ящик или полку дома.", "Напишите три вещи, за которые вы благодарны сегодня.",
    "Сделайте комплимент трём людям.", "Выучите пять слов на иностранном языке.",
    "Сделайте планку на 30 секунд, потом на минуту.", "Пройдите 5000 шагов сегодня.",
    "Послушайте альбом, который раньше не слушали.", "Прочитайте 10 страниц книги.",
    "Сегодня ни одной сладкой газировки.", "Сфотографируйте что-нибудь красивое вокруг.",
    "Позвоните родителям или бабушке с дедушкой.", "Лягте спать на час раньше обычного.",
    "Сделайте растяжку на 10 минут.", "Напишите план на завтра из трёх пунктов.",
    "Помогите кому-нибудь с мелочью.", "Уберите рабочий стол.", "Посмотрите фильм, который давно откладывали.",
    "Улыбнитесь незнакомцу.", "Выпейте за день два литра воды.", "Сделайте 20 отжиманий за день (можно в несколько подходов).",
    "Удалите из телефона 20 ненужных фото.", "Отдохните от соцсетей на два часа.",
    "Научитесь чему-то новому по видео на 10 минут.", "Придумайте и расскажите другу шутку.",
    "Проветрите комнату и сделайте 10 глубоких вдохов.", "Напишите письмо себе в будущее.",
    "Приготовьте полезный завтрак.", "Потанцуйте под любимую песню.", "Позвоните старому другу.",
    "Прогуляйтесь в парк или к воде.", "Сделайте что-то, что откладывали уже неделю.",
    "Составьте плейлист для хорошего настроения.", "Попробуйте новый напиток или блюдо.",
    "Сегодня говорите «спасибо» каждому, кто вам помог.",
]


def chal_of_day() -> str:
    return CHALLENGES[today().toordinal() % len(CHALLENGES)]


def claim_chal(uid: int, name=None) -> tuple[bool, int, int]:
    a = acct(uid, name)
    d = today().isoformat()
    if a["chal_day"] == d:
        return False, 0, a["chal_streak"]
    yest = (today() - timedelta(days=1)).isoformat()
    a["chal_streak"] = a["chal_streak"] + 1 if a["chal_day"] == yest else 1
    amount = 150 + 30 * (min(a["chal_streak"], 7) - 1)
    a["chal_day"] = d
    a["coins"] += amount
    _save_econ()
    return True, amount, a["chal_streak"]


def profile_view(uid: int) -> tuple[str, InlineKeyboardMarkup]:
    a = acct(uid)
    d = today().isoformat()
    bonus = "уже получен ✅" if a["last_bonus"] == d else "можно забрать 🎁"
    chal = "выполнен ✅" if a["chal_day"] == d else "ждёт вас 🎯"
    text = (f"👤 <b>{shown(uid)}</b>\n{LINE}\n"
            f"💰 Монеты: <b>{a['coins']}</b>\n"
            f"🏅 Побед в играх: <b>{a['wins']}</b>\n"
            f"🎁 Бонус: {bonus} (серия {a['streak']} дн.)\n"
            f"🎯 Челлендж дня: {chal} (серия {a['chal_streak']} дн.)")
    return text, _kb([("🎁 Бонус", "e:bonus"), ("🎯 Челлендж", "e:chal")],
                     [("🛒 Магазин", "e:shop"), ("🏆 Лидеры", "e:top")], [("‹ Меню", "m:home")])


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


def leaders_text(mode: str) -> str:
    rows = [(uid, a) for uid, a in ECON.items()]
    key = "coins" if mode == "c" else "wins"
    rows = sorted([r for r in rows if r[1][key] > 0], key=lambda r: -r[1][key])[:10]
    title = "💰 Самые богатые" if mode == "c" else "🏅 Больше всех побед"
    body = "\n".join(f"{MEDALS[i] if i < 3 else f'{i + 1}.'} {shown(uid)} — <b>{a[key]}</b>"
                     for i, (uid, a) in enumerate(rows)) or "Пока пусто."
    return f"🏆 <b>{title}</b>\n{LINE}\n{body}"


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
    elif action == "chal":
        await q.answer()
        a = acct(user.id)
        done = a["chal_day"] == today().isoformat()
        text = (f"🎯 <b>Челлендж дня</b>\n{LINE}\n{esc(chal_of_day())}\n\n"
                + ("✅ Вы уже выполнили его сегодня. Новый будет завтра." if done else
                   "Выполните задание и нажмите кнопку. За серию дней награда растёт."))
        kb = _kb([("✅ Выполнил(а)", "e:chaldone")] if not done else [], [("‹ Профиль", "e:profile")])
        await show(q, text, kb)
    elif action == "chaldone":
        ok, amount, streak = claim_chal(user.id, _name(user))
        await q.answer(f"🎯 +{amount} монет! Серия: {streak} дн." if ok else "Сегодня уже засчитано 🙂",
                       show_alert=True)
        await show(q, *profile_view(user.id))
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
    elif action == "top":
        mode = parts[1] if len(parts) > 1 else "c"
        await q.answer()
        kb = _kb([("💰 Богатство", "e:top:c"), ("🏅 Победы", "e:top:w")], [("‹ Профиль", "e:profile")])
        await show(q, leaders_text("w" if mode == "w" else "c"), kb)
    else:
        await q.answer()


MEDALS = ["🥇", "🥈", "🥉"]



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


async def morning_text(city: str | None = None, news: str | None = None) -> str:
    d = datetime.now(TZ)
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
    return _kb([("🎁 Забрать бонус", "e:bonus"), ("🎯 Челлендж", "e:chal")], [(label, "m:mtoggle")],
               [("‹ Меню", "m:home")])


async def send_morning(context: ContextTypes.DEFAULT_TYPE):
    """Каждое утро: владельцу и друзьям, у кого рассылка не выключена."""
    news = await asyncio.to_thread(_fetch_news)
    cache: dict[str, str] = {}
    for uid in subscribers("morning"):
        city = city_of(uid)
        if city not in cache:
            cache[city] = await morning_text(city, news)
        try:
            await context.bot.send_message(uid, cache[city], parse_mode="HTML",
                                           disable_web_page_preview=True, reply_markup=morning_kb(uid))
        except Exception:
            log.exception("утренняя сводка не доставлена: %s", uid)
        await asyncio.sleep(0.1)


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
    rows = [[("🗣 Правда", "game:td:truth"), ("🎬 Действие", "game:td:dare")], [("🎲 Случайно", "game:td:rand")]]
    if adult_ok(uid):
        rows.append([(f"🎚 Уровень: {LEVEL_NAME[level_of(uid)]}", "game:adult")])
    rows.append([("‹ Меню", "m:home")])
    return _kb(*rows)


def pick_td(kind: str, level: str) -> str:
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
            [("🎭 Правда или действие", "m:td")],
            [("👤 Профиль", "e:profile"), ("💡 Помощь", "m:help")]]
    if is_owner(uid):
        rows.append([("👥 Друзья и группы", "m:friends")])
    return _kb(*rows)


def welcome_text() -> str:
    file_mb = FRIEND_MAX_MB if LOCAL_API_URL else min(FRIEND_MAX_MB, 20)
    return (
        f"✨ <b>Привет! Я ваш карманный помощник</b>\n{LINE}\n"
        "📥 Ссылка TikTok, Reels или YouTube: пришлю видео, YouTube ещё и MP3\n"
        "🎞 Видео-файл: сожму или достану звук. Картинка: PDF, стикер или чтение QR\n"
        "🔲 /qr текст: сделаю QR-код\n"
        f"🌦 Погода сейчас и через 2, 4, 6 часов (по умолчанию {esc(FRIEND_CITY)})\n"
        f"☀️ Утренняя карточка в {MORNING_TIME}: праздник, факт дня, погода, курсы и новости\n"
        "☔ Предупрежу за полчаса до дождя\n"
        "🎭 Правда или действие с тремя уровнями\n"
        "👤 Монеты, бонус каждый день, челлендж и магазин званий\n"
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
    "👤 Профиль: монеты, бонус, челлендж, магазин, лидеры\n\n"
    f"👑 <b>Для владельца</b>\n{LINE}\n"
    "👥 /friends: друзья и группы, 🔞 уровни\n"
    "➕ /add ID: добавить друга вручную\n"
    "💬 В группах: /games (игры, казино, мафия, викторины, дуэли), /top (лидеры), /ask (анонимный вопрос)"
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
    if not is_allowed(uid):                               # гость по игровой ссылке
        await update.message.reply_text(
            "👋 Привет! Теперь я смогу присылать вам роли в играх и передавать анонимные вопросы.\n"
            "Остальные функции доступны по приглашению владельца бота.")
        return
    acct(uid, update.effective_user.full_name)
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
            [("🎬 Видео", "yt:video"), ("🎵 MP3", "yt:audio")]))
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
        if url:
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
               "🎮 /games: игры, казино, мафия, викторины, дуэли\n🏆 /top: лидеры группы\n"
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
               [("🎁 Бонус", "e:bonus"), ("🏆 Лидеры", "gg:top:w")],
               [("🙋 Я в компании", "gg:here")])


GAMES_TITLE = f"🎮 <b>Игры для компании</b>\n{LINE}\nВыбирайте, во что играем:"


async def games_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(GAMES_TITLE, parse_mode="HTML", reply_markup=games_kb())


async def group_help(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(GROUP_HELLO, parse_mode="HTML", reply_markup=games_kb())


def _rows(items: list[tuple[int, str, int]]) -> str:
    items = sorted(items, key=lambda x: -x[2])[:10]
    return "\n".join(f"{MEDALS[i] if i < 3 else f'{i + 1}.'} {shown(u, n)} — <b>{v}</b>"
                     for i, (u, n, v) in enumerate(items))


def board_text(chat_id: int, mode: str) -> str:
    if mode == "c":
        rows = [(u, n, acct(u)["coins"]) for u, n in cands(chat_id)]
        return f"💰 <b>Самые богатые в группе</b>\n{LINE}\n" + (_rows(rows) or "Пока пусто.")
    rows = [(u, r["name"], r["wins"]) for u, r in STATS["group"].get(chat_id, {}).items() if r["wins"] > 0]
    return f"🏅 <b>Лидеры группы по победам</b>\n{LINE}\n" + (_rows(rows) or "Пока пусто. Сыграйте в /games!")


def board_kb() -> InlineKeyboardMarkup:
    return _kb([("🏅 Победы", "gg:top:w"), ("💰 Богачи", "gg:top:c")], [("‹ Игры", "gg:menu")])


async def top_group_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(board_text(update.effective_chat.id, "w"), parse_mode="HTML",
                                              reply_markup=board_kb())


async def top_private(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(leaders_text("c"), parse_mode="HTML")


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
            reward(q.message.chat.id, win_id, win_name, 50)
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
            reward(chat, w, wn, st["pot"])
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
            reward(chat, u, names[u], 100)
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
    elif action == "top":
        await q.answer()
        await show(q, board_text(chat.id, args[0] if args else "w"), board_kb())
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
            reward(chat, u, name, 150)
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
    user_cmds = [BotCommand("start", "🏠 Меню"), BotCommand("weather", "🌦 Погода"), BotCommand("morning", "☀️ Сводка"),
                 BotCommand("rain", "☔ Дождь вкл/выкл"), BotCommand("qr", "🔲 Сделать QR-код"),
                 BotCommand("top", "🏆 Лидеры")]
    owner_cmds = user_cmds + [BotCommand("friends", "👥 Друзья и группы"), BotCommand("add", "➕ Добавить друга по ID")]
    group_cmds = [BotCommand("games", "🎮 Игры для компании"), BotCommand("top", "🏆 Лидеры группы"),
                  BotCommand("ask", "💌 Анонимный вопрос")]
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
    app.add_handler(CallbackQueryHandler(on_game, pattern=r"^game:"))
    app.add_handler(CallbackQueryHandler(on_gg, pattern=r"^gg:"))
    app.add_handler(CallbackQueryHandler(on_mf, pattern=r"^mf:"))
    app.add_handler(CallbackQueryHandler(on_button, pattern=r"^(yt|conv):"))
    hh, mm = map(int, MORNING_TIME.split(":"))
    app.job_queue.run_daily(send_morning, time(hh, mm, tzinfo=TZ))
    app.job_queue.run_repeating(check_rain, interval=600, first=30)   # проверка дождя каждые 10 минут
    app.run_polling()


if __name__ == "__main__":
    main()
