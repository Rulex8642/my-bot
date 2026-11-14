"""Telegram-бот: скачивание видео, конвертер, QR, стикеры, погода. Владелец + друзья по списку."""
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
from datetime import time
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
            if len(recent) >= 40:                            # не больше 40 нажатий в минуту на группу
                MSGS[chat.id] = recent
                raise ApplicationHandlerStop
            recent.append(now)
            MSGS[chat.id] = recent
        return
    if not is_allowed(user.id):
        if user.id not in USERS["blocked"] and not update.callback_query:
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
            "⏳ В очереди, скоро начну..." if HEAVY.locked() else "⏳ Скачиваю...")
        async with HEAVY:
            path = await asyncio.to_thread(_download, url, audio, tmp, not is_owner(uid))
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
            "⏳ В очереди, скоро начну..." if HEAVY.locked() else "⏳ Обрабатываю...")
        tg_file = await context.bot.get_file(fid)    # лимит скачивания у бота — 20 МБ
        if not is_owner(update.effective_user.id) and (tg_file.file_size or 0) > FRIEND_MAX_MB * 1024 * 1024:
            raise RuntimeError(f"Файл больше {FRIEND_MAX_MB} МБ.")
        src = tmp / "input"
        async with HEAVY:
            await tg_file.download_to_drive(src)
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


async def morning_text(city: str | None = None, news: str | None = None) -> str:
    try:
        weather = await get_weather(city)
    except Exception:
        weather = "Погоду получить не удалось."
    if news is None:
        news = await asyncio.to_thread(_fetch_news)
    return f"☀️ <b>Доброе утро!</b>\n\n{weather}\n\n📰 <b>Главное в мире:</b>\n{news}"


def morning_kb(uid: int) -> InlineKeyboardMarkup:
    label = "🔕 Не присылать по утрам" if pref(uid, "morning") else "🔔 Присылать по утрам"
    return InlineKeyboardMarkup([[InlineKeyboardButton(label, callback_data="menu:morning")]])


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


# ---------- хендлеры ----------
BTN_VIDEO, BTN_FILE, BTN_QR = "📥 Скачать видео", "🎞 Конвертер", "🔲 QR-код"
BTN_WEATHER, BTN_HELP = "🌦 Погода", "💡 Помощь"
BTN_GAMES, BTN_TOP = "🎮 Игры", "🏆 Лидеры"
BTN_MORNING, BTN_RAIN, BTN_FRIENDS = "☀️ Сводка", "☔ Дождь", "👥 Друзья"


def main_menu(uid: int) -> ReplyKeyboardMarkup:
    rows = [[BTN_VIDEO, BTN_FILE], [BTN_WEATHER, BTN_MORNING], [BTN_GAMES, BTN_TOP], [BTN_QR, BTN_RAIN]]
    rows.append([BTN_HELP, BTN_FRIENDS] if is_owner(uid) else [BTN_HELP])
    return ReplyKeyboardMarkup(rows, resize_keyboard=True, is_persistent=True,
                               input_field_placeholder="Пришлите ссылку или файл ✨")


def welcome_text() -> str:
    file_mb = FRIEND_MAX_MB if LOCAL_API_URL else min(FRIEND_MAX_MB, 20)
    return (
        f"✨ <b>Привет! Я твой карманный помощник</b>\n{LINE}\n"
        "📥 <b>Видео</b> — пришли ссылку TikTok, Reels или YouTube\n"
        "🎞 <b>Конвертер</b> — сжать видео, достать MP3, сделать PDF или стикер\n"
        "🔲 <b>QR</b> — создам код или прочитаю с картинки\n"
        f"🌦 <b>Погода</b> — сейчас и через 2, 4, 6 часов (по умолчанию {esc(FRIEND_CITY)})\n"
        f"☀️ <b>Сводка</b> — каждое утро в {MORNING_TIME}: погода и новости\n"
        "☔ <b>Дождь</b> — предупрежу за полчаса\n"
        "🎮 <b>Игры</b> — монетка, кубик, правда или действие, шар, КНБ, угадай число\n"
        "🏆 <b>Лидеры</b> — кто чаще всех побеждает\n\n"
        f"📋 <b>Правила и лимиты</b>\n{LINE}\n"
        f"• до {FRIEND_JOBS_PER_HOUR} скачиваний и конвертаций в час, по одной за раз\n"
        f"• видео до {FRIEND_MAX_MIN} мин и {FRIEND_MAX_MB} МБ, без прямых эфиров\n"
        f"• файлы для конвертации до {file_mb} МБ\n"
        "• ссылки только YouTube, TikTok и Instagram\n"
        "• не больше 20 сообщений в минуту\n"
        "• при большой нагрузке задачи ждут в очереди\n"
        "• сводку и дождь можно выключить кнопками\n"
        "• владелец может отозвать доступ в любой момент\n\n"
        "👇 <i>Кнопки внизу — всё под рукой</i>"
    )


HELP = (
    f"💡 <b>Что я умею</b>\n{LINE}\n"
    "📥 Ссылка TikTok / Reels / YouTube — видео или MP3\n"
    "🎞 Видео-файл — сжать или вытащить MP3\n"
    "🖼 Картинка — PDF, стикер или чтение QR\n"
    "🔲 /qr текст — сделать QR-код\n"
    "🌦 /weather — погода сейчас и через 2, 4, 6 часов\n"
    f"☀️ /morning — сводка сейчас (сама приходит в {MORNING_TIME})\n"
    "☔ /rain — оповещения о дожде вкл/выкл\n"
    "🎮 Игры: монетка, кубик, дуэль кубиков, правда или действие (3 уровня), шар, КНБ, угадай число\n"
    "🏆 /top — таблица лидеров (в группе — лидеры группы)\n\n"
    f"👑 <b>Для владельца</b>\n{LINE}\n"
    "👥 /friends — друзья и группы: удалить, разблокировать, 🔞 уровни\n"
    "➕ /add ID — добавить друга вручную\n"
    "💬 Группы: добавьте бота в чат, там работают /games и /top"
)


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    await update.message.reply_text(HELP if is_owner(uid) else welcome_text(), parse_mode="HTML",
                                    reply_markup=main_menu(uid))


async def send_weather(update: Update, context: ContextTypes.DEFAULT_TYPE, city: str, remember: bool = False):
    try:
        text = await get_forecast(city=city)
        if remember:
            context.user_data["city"] = city            # запомним для следующего раза
    except LookupError:
        text = "Не нашёл такой город. Нажмите «Другой город» и попробуйте написать иначе."
    except Exception:
        log.exception("forecast failed")
        text = "Не удалось получить прогноз, попробуйте позже."
    kb = InlineKeyboardMarkup([[InlineKeyboardButton("🏙 Другой город", callback_data="menu:city")]])
    await update.effective_message.reply_text(text, reply_markup=kb)


async def weather_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    arg = " ".join(context.args or []).strip()[:60]
    uid = update.effective_user.id
    city = arg or (CITY if is_owner(uid) else context.user_data.get("city") or FRIEND_CITY)
    await send_weather(update, context, city, remember=bool(arg))


async def morning_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    await update.effective_message.reply_text(
        await morning_text(city_of(uid)), parse_mode="HTML",
        disable_web_page_preview=True, reply_markup=morning_kb(uid))


async def on_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    text = (update.message.text or "").strip()
    action = MENU.get(text)
    if action:                                        # нажата кнопка меню
        context.user_data.pop("await", None)
        context.user_data.pop("guess", None)
        await action(update, context)
        return
    if "guess" in context.user_data and text.isdigit() and len(text) <= 6:
        await guess_try(update, context, int(text))
        return
    mode = context.user_data.pop("await", None)       # бот ждал ответа после кнопки
    if mode == "ball":
        await update.message.reply_text(f"🔮 {random.choice(BALL)}",
                                        reply_markup=_kb([("🔮 Ещё вопрос", "game:ball"), ("🎮 Все игры", "game:menu")]))
        return
    if mode == "qr":
        await send_qr(update, text)
        return
    if mode == "city":
        await send_weather(update, context, text[:60], remember=True)
        return
    m = URL_RE.search(text)
    if not m:
        await update.message.reply_text("Пришлите ссылку или файл либо выберите действие в меню внизу.")
        return
    url = m.group(0)
    if not url_allowed(url, update.effective_user.id):
        await update.message.reply_text("Поддерживаются ссылки YouTube, TikTok и Instagram.")
        return
    if "youtube.com" in url or "youtu.be" in url:
        context.user_data["url"] = url
        kb = InlineKeyboardMarkup([[
            InlineKeyboardButton("🎬 Видео", callback_data="yt:video"),
            InlineKeyboardButton("🎵 MP3", callback_data="yt:audio"),
        ]])
        await update.message.reply_text("Что скачать?", reply_markup=kb)
    else:                                             # TikTok, Instagram и всё остальное
        await download_and_send(update, url)


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
                                       parse_mode="HTML", reply_markup=main_menu(uid))
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


# ---------- мини-игры ----------
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
LEVELS = ["lite", "mid", "hot"]
LEVEL_NAME = {"lite": "😊 Лёгкий", "mid": "😏 Средний", "hot": "🔥 Горячий"}
LEVEL_POOLS = {"lite": ("TRUTHS", "DARES"), "mid": ("SPICY_TRUTHS", "SPICY_DARES"), "hot": ("HOT_TRUTHS", "HOT_DARES")}
BALL = [
    "Бесспорно", "Предрешено", "Никаких сомнений", "Определённо да", "Можешь быть уверен(а)",
    "Мне кажется, да", "Вероятнее всего", "Хорошие перспективы", "Знаки говорят «да»", "Да",
    "Пока не ясно, попробуй снова", "Спроси позже", "Лучше не рассказывать", "Сейчас нельзя предсказать",
    "Сконцентрируйся и спроси опять", "Даже не думай", "Мой ответ «нет»", "По моим данным «нет»",
    "Перспективы не очень", "Весьма сомнительно",
]
RPS = {"r": "🪨 Камень", "s": "✂️ Ножницы", "p": "📄 Бумага"}
RPS_BEATS = {"r": "s", "s": "p", "p": "r"}          # что побеждает что
RPS_KB = InlineKeyboardMarkup([[InlineKeyboardButton(n, callback_data=f"game:rps:{k}") for k, n in RPS.items()]])


def _kb(*rows) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[InlineKeyboardButton(t, callback_data=d) for t, d in row] for row in rows])


GAMES_KB = _kb(
    [("🪙 Монетка", "game:coin"), ("🎲 Кубик", "game:dice")],
    [("🎭 Правда или действие", "game:td")],
    [("🔮 Магический шар", "game:ball"), ("✂️ Камень-ножницы-бумага", "game:rps")],
    [("🔢 Угадай число", "game:guess"), ("⚔️ Дуэль кубиков", "game:duel")],
    [("🏆 Таблица лидеров", "game:top")],
)
GAMES_TITLE = f"🎮 <b>Игры</b>\n{LINE}\nВо что сыграем?"


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
    return _kb(*rows)


def pick_td(kind: str, level: str) -> str:
    truths, dares = (globals()[n] for n in LEVEL_POOLS[level])
    text = random.choice(truths) if kind == "truth" else random.choice(dares)
    return text.replace("{other}", "игрока, который согласится")


async def m_games(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(GAMES_TITLE, parse_mode="HTML", reply_markup=GAMES_KB)


async def on_game(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    if not is_allowed(q.from_user.id) or q.message.chat.type != "private":
        return
    msg, ud = q.message, context.user_data
    parts = q.data.split(":")[1:]
    game, arg = parts[0], (parts[1] if len(parts) > 1 else None)
    if game == "menu":
        await msg.reply_text(GAMES_TITLE, parse_mode="HTML", reply_markup=GAMES_KB)
    elif game == "top":
        await msg.reply_text(solo_board(q.from_user.id), parse_mode="HTML")
    elif game == "coin":
        await msg.reply_text(f"🪙 {random.choice(['Орёл', 'Решка'])}!",
                             reply_markup=_kb([("🪙 Ещё раз", "game:coin"), ("🎮 Все игры", "game:menu")]))
    elif game == "dice":
        await msg.reply_text("🎲 <b>Что бросаем?</b>", parse_mode="HTML", reply_markup=_kb(
            [(e, f"game:roll:{e}") for e in ("🎲", "🎯", "🏀")], [(e, f"game:roll:{e}") for e in ("⚽", "🎳", "🎰")],
            [("⚔️ Дуэль кубиков со мной", "game:duel")]))
    elif game == "duel":
        mine = await msg.reply_dice(emoji="🎲")             # первый кубик ваш, второй мой
        theirs = await msg.reply_dice(emoji="🎲")
        a, b = mine.dice.value, theirs.dice.value
        await asyncio.sleep(4)                              # ждём конца анимации
        if a > b:
            add_solo_win(q.from_user.id, q.from_user.full_name, "duel")
            verdict = "🎉 Вы выиграли!"
        elif a < b:
            verdict = "😎 Я выиграл!"
        else:
            verdict = "🤝 Ничья!"
        await msg.reply_text(f"⚔️ <b>Дуэль кубиков</b>\n{LINE}\nВы: <b>{a}</b>   Я: <b>{b}</b>\n{verdict}",
                             parse_mode="HTML", reply_markup=_kb([("⚔️ Ещё раз", "game:duel"), ("🎮 Все игры", "game:menu")]))
    elif game == "roll":
        if arg in ("🎲", "🎯", "🏀", "⚽", "🎳", "🎰"):
            await msg.reply_dice(emoji=arg)
    elif game == "td":
        uid = q.from_user.id
        if arg is None:
            lvl = level_of(uid)
            await msg.reply_text(f"🎭 <b>Правда или действие</b>\n{LINE}\nУровень: {LEVEL_NAME[lvl]}",
                                 parse_mode="HTML", reply_markup=td_kb(uid))
        else:
            kind = random.choice(("truth", "dare")) if arg == "rand" else arg
            lvl = level_of(uid)
            head = "🗣 <b>Правда</b>" if kind == "truth" else "🎬 <b>Действие</b>"
            tag = {"lite": "", "mid": "🔞 ", "hot": "🔥 "}[lvl]
            text = f"{tag}{head}\n{LINE}\n{html.escape(pick_td(kind, lvl))}"
            if lvl != "lite":
                text += "\n\n<i>Любой игрок вправе пропустить вопрос или задание.</i>"
            await msg.reply_text(text, parse_mode="HTML", reply_markup=td_kb(uid))
    elif game == "adult":
        uid = q.from_user.id
        prefs = USERS["prefs"].setdefault(uid, {})
        if not adult_ok(uid):
            await msg.reply_text("Этот режим для вас недоступен.")
        elif not prefs.get("adult"):
            await msg.reply_text(
                "🔞 Уровни «Средний» и «Горячий» только для совершеннолетних: вопросы и задания будут "
                "пикантными, а некоторые зададут игроку физический контакт по согласию. Вам есть 18 лет?",
                reply_markup=_kb([("✅ Да, мне есть 18", "game:adult18:yes"), ("❌ Нет", "game:adult18:no")]))
        else:
            nxt = LEVELS[(LEVELS.index(level_of(uid)) + 1) % len(LEVELS)]
            prefs["level"] = nxt
            _save_users()
            await msg.reply_text(f"🎚 Уровень: {LEVEL_NAME[nxt]}", reply_markup=td_kb(uid))
    elif game == "adult18":
        uid = q.from_user.id
        if arg == "yes" and adult_ok(uid):
            prefs = USERS["prefs"].setdefault(uid, {})
            prefs["adult"], prefs["level"] = True, "mid"
            _save_users()
            await msg.reply_text("🔞 Режим включён: уровень «Средний». Меняйте уровень кнопкой ниже. "
                                 "Играйте только со взрослыми и по согласию: пропустить можно любой вопрос.",
                                 reply_markup=td_kb(uid))
        else:
            await msg.reply_text("Хорошо, остаёмся на лёгком уровне.", reply_markup=td_kb(uid))
    elif game == "ball":
        ud["await"] = "ball"
        await msg.reply_text("🔮 Задайте вопрос, на который можно ответить «да» или «нет», и напишите его мне.")
    elif game == "rps":
        if arg not in RPS:
            await msg.reply_text("Выбирайте:", reply_markup=RPS_KB)
            return
        mine = random.choice(list(RPS))
        score = ud.setdefault("rps", [0, 0, 0])             # победы, поражения, ничьи
        if arg == mine:
            result, score[2] = "Ничья!", score[2] + 1
        elif RPS_BEATS[arg] == mine:
            result, score[0] = "Вы выиграли! 🎉", score[0] + 1
            add_solo_win(q.from_user.id, q.from_user.full_name, "rps")
        else:
            result, score[1] = "Я выиграл 😎", score[1] + 1
        await msg.reply_text(f"Вы: {RPS[arg]}\nЯ: {RPS[mine]}\n{result}\n"
                             f"Счёт: {score[0]} побед, {score[1]} поражений, {score[2]} ничьих", reply_markup=RPS_KB)
    elif game == "guess":
        ud["guess"] = {"n": random.randint(1, 100), "tries": 0}
        await msg.reply_text("🔢 Я загадал число от 1 до 100. Пишите варианты, я подскажу «больше» или «меньше».")


async def guess_try(update: Update, context: ContextTypes.DEFAULT_TYPE, number: int):
    g = context.user_data["guess"]
    g["tries"] += 1
    if number == g["n"]:
        context.user_data.pop("guess")
        add_solo_win(update.effective_user.id, update.effective_user.full_name, "guess")
        await update.message.reply_text(f"🎉 Угадали число {number}! Попыток: {g['tries']}",
                                        reply_markup=_kb([("🔢 Ещё раз", "game:guess"), ("🎮 Все игры", "game:menu")]))
    else:
        await update.message.reply_text("Моё число больше ⬆️" if number < g["n"] else "Моё число меньше ⬇️")


# ---------- таблицы лидеров ----------
MEDALS = ["🥇", "🥈", "🥉"]


def _rows(items: list[tuple[str, int]]) -> str:
    items = sorted(items, key=lambda x: -x[1])[:10]
    return "\n".join(f"{MEDALS[i] if i < 3 else f'{i + 1}.'} {esc(n)} — <b>{w}</b>" for i, (n, w) in enumerate(items))


def solo_board(uid: int) -> str:
    rows = [(r["name"], r["wins"]) for r in STATS["solo"].values() if r["wins"] > 0]
    text = f"🏆 <b>Таблица лидеров</b>\n<i>победы над ботом</i>\n{LINE}\n"
    text += _rows(rows) if rows else "Пока пусто. Сыграйте с ботом в «✂️ Камень-ножницы-бумага», «🔢 Угадай число» или «⚔️ Дуэль кубиков»!"
    me = STATS["solo"].get(uid)
    if me and me["wins"] > 0:
        place = 1 + sum(1 for r in STATS["solo"].values() if r["wins"] > me["wins"])
        names = {"rps": "КНБ", "guess": "числа", "duel": "дуэли"}
        detail = ", ".join(f"{names.get(g, g)}: {n}" for g, n in sorted(me["games"].items()))
        text += f"\n{LINE}\nВы: <b>{me['wins']}</b> побед, место №{place} ({detail})"
    return text


def group_board(chat_id: int) -> str:
    rows = [(r["name"], r["wins"]) for r in STATS["group"].get(chat_id, {}).values() if r["wins"] > 0]
    text = f"🏆 <b>Лидеры группы</b>\n{LINE}\n"
    return text + (_rows(rows) if rows else "Пока пусто. Сыграйте в /games!")


async def top_private(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(solo_board(update.effective_user.id), parse_mode="HTML")


# ---------- игры для групп ----------
GG: dict[tuple[int, int], dict] = {}              # (чат, сообщение) -> состояние игры
GROUP_PENDING: dict[int, str] = {}                # группы, ждущие решения владельца
GROUP_HELLO = ("👋 <b>Привет! Я бот с играми для компании.</b>\n"
               f"{LINE}\n/games — выбрать игру\n/top — таблица лидеров группы")


def gg_put(key: tuple[int, int], st: dict):
    if len(GG) > 300:
        GG.pop(next(iter(GG)))
    GG[key] = st


def gg_menu_kb() -> InlineKeyboardMarkup:
    return _kb([("🎲 Кубики", "gg:new:dice"), ("⚔️ Дуэль КНБ", "gg:new:rps")],
               [("🪙 Орёл или решка", "gg:new:coin"), ("🔢 Угадай число", "gg:new:num")],
               [("🏆 Таблица лидеров", "gg:top")])


async def games_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(
        f"🎮 <b>Игры для компании</b>\n{LINE}\nВыбирайте, во что играем:", parse_mode="HTML", reply_markup=gg_menu_kb())


async def top_group_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(group_board(update.effective_chat.id), parse_mode="HTML")


async def group_help(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(GROUP_HELLO, parse_mode="HTML")


def _name(user) -> str:
    return user.full_name or user.first_name or str(user.id)


# --- кубики
def dice_text(st: dict) -> str:
    lines = [f"{'🎲 ' + str(v) if v else '🎲 бросает…'} — {esc(n)}" for n, v in st["throws"].values()]
    body = "\n".join(lines) if lines else "Пока никто не бросал."
    return (f"🎲 <b>Кубики: у кого больше?</b>\n{LINE}\n{body}\n\n"
            f"<i>Ведущий: {esc(st['host_name'])}. Когда все бросили, он нажимает «Итоги».</i>")


DICE_KB = lambda: _kb([("🎲 Бросить", "gg:roll"), ("🏁 Итоги", "gg:end")])


async def gg_dice(q, st, action, arg):
    user = q.from_user
    if action == "roll":
        if user.id in st["throws"]:
            await q.answer("Вы уже бросали 🙂")
            return
        st["throws"][user.id] = (_name(user), 0)
        await q.answer()
        m = await q.message.reply_dice(emoji="🎲")
        st["throws"][user.id] = (_name(user), m.dice.value)
        await asyncio.sleep(3.5)                            # ждём конца анимации
        try:
            await q.message.edit_text(dice_text(st), parse_mode="HTML", reply_markup=DICE_KB())
        except Exception:
            pass
    elif action == "end":
        if user.id not in (st["host"], OWNER_ID):
            await q.answer("Итоги подводит ведущий", show_alert=True)
            return
        done = [(uid, n, v) for uid, (n, v) in st["throws"].items() if v]
        if len(done) < 2:
            await q.answer("Нужно минимум два броска", show_alert=True)
            return
        await q.answer()
        top = max(v for _, _, v in done)
        winners = [(uid, n) for uid, n, v in done if v == top]
        if len(winners) == 1:
            add_group_win(q.message.chat.id, winners[0][0], winners[0][1])
            verdict = f"🏆 Победитель: <b>{esc(winners[0][1])}</b> ({top})"
        else:
            verdict = "🤝 Ничья между: " + ", ".join(esc(n) for _, n in winners) + " (очки не начисляются)"
        GG.pop((q.message.chat.id, q.message.message_id), None)
        await q.message.edit_text(dice_text(st).split("\n\n<i>")[0] + f"\n\n{verdict}", parse_mode="HTML")


# --- дуэль камень-ножницы-бумага
def rps_text(st: dict) -> str:
    p1, p2 = st["p1"][1], st["p2"][1] if st["p2"] else None
    if p2 is None:
        return f"⚔️ <b>Дуэль: камень-ножницы-бумага</b>\n{LINE}\n{esc(p1)} вызывает на дуэль! Кто примет вызов?"
    chosen = lambda uid: "✅ выбрал(а)" if uid in st["choices"] else "⏳ думает"
    return (f"⚔️ <b>Дуэль: камень-ножницы-бумага</b>\n{LINE}\n"
            f"{esc(p1)} — {chosen(st['p1'][0])}\n{esc(p2)} — {chosen(st['p2'][0])}\n\n<i>Выбор видите только вы.</i>")


RPS_PICK_KB = lambda: _kb([("🪨 Камень", "gg:pick:r"), ("✂️ Ножницы", "gg:pick:s"), ("📄 Бумага", "gg:pick:p")])


async def gg_rps(q, st, action, arg):
    user = q.from_user
    players = [st["p1"][0]] + ([st["p2"][0]] if st["p2"] else [])
    if action == "join":
        if st["p2"] is not None or user.id == st["p1"][0]:
            await q.answer("Вызов уже принят" if st["p2"] else "Нужен соперник, а не вы 🙂", show_alert=True)
            return
        st["p2"] = (user.id, _name(user))
        await q.answer()
        await q.message.edit_text(rps_text(st), parse_mode="HTML", reply_markup=RPS_PICK_KB())
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
            await q.message.edit_text(rps_text(st), parse_mode="HTML", reply_markup=RPS_PICK_KB())
            return
        (u1, n1), (u2, n2) = st["p1"], st["p2"]
        c1, c2 = st["choices"][u1], st["choices"][u2]
        if c1 == c2:
            verdict = "🤝 Ничья!"
        else:
            win_id, win_name = (u1, n1) if RPS_BEATS[c1] == c2 else (u2, n2)
            add_group_win(q.message.chat.id, win_id, win_name)
            verdict = f"🏆 Победил(а): <b>{esc(win_name)}</b>"
        st["done"] = True
        await q.message.edit_text(
            f"⚔️ <b>Дуэль: камень-ножницы-бумага</b>\n{LINE}\n{esc(n1)}: {RPS[c1]}\n{esc(n2)}: {RPS[c2]}\n\n{verdict}",
            parse_mode="HTML", reply_markup=_kb([("🔁 Реванш", "gg:again")]))
    elif action == "again":
        if user.id not in players or not st.get("done"):
            await q.answer("Реванш для участников после раунда", show_alert=True)
            return
        st["choices"], st["done"] = {}, False
        await q.answer()
        await q.message.edit_text(rps_text(st), parse_mode="HTML", reply_markup=RPS_PICK_KB())


# --- орёл или решка
def coin_text(st: dict) -> str:
    side = {"h": "🦅 Орёл", "t": "🪙 Решка"}
    lines = [f"{side[b]} — {esc(n)}" for n, b in st["bets"].values()]
    body = "\n".join(lines) if lines else "Ставок пока нет."
    return (f"🪙 <b>Орёл или решка</b>\n{LINE}\n{body}\n\n"
            f"<i>Ведущий: {esc(st['host_name'])}. Ставку можно менять, пока он не бросил монету.</i>")


COIN_KB = lambda: _kb([("🦅 Орёл", "gg:bet:h"), ("🪙 Решка", "gg:bet:t")], [("🎯 Бросить монету", "gg:flip")])


async def gg_coin(q, st, action, arg):
    user = q.from_user
    if action == "bet" and arg in ("h", "t"):
        st["bets"][user.id] = (_name(user), arg)
        await q.answer("Ставка принята")
        try:
            await q.message.edit_text(coin_text(st), parse_mode="HTML", reply_markup=COIN_KB())
        except Exception:
            pass                                             # та же ставка: текст не изменился
    elif action == "flip":
        if user.id not in (st["host"], OWNER_ID):
            await q.answer("Монету бросает ведущий", show_alert=True)
            return
        if len(st["bets"]) < 2:
            await q.answer("Нужно минимум два игрока со ставками", show_alert=True)
            return
        await q.answer()
        res = random.choice(("h", "t"))
        winners = [(uid, n) for uid, (n, b) in st["bets"].items() if b == res]
        losers = len(st["bets"]) - len(winners)
        if winners and losers:
            for uid, n in winners:
                add_group_win(q.message.chat.id, uid, n)
            verdict = "🏆 Угадали: " + ", ".join(f"<b>{esc(n)}</b>" for _, n in winners)
        else:
            verdict = "Все выбрали одно и то же, очки не начисляются."
        GG.pop((q.message.chat.id, q.message.message_id), None)
        await q.message.edit_text(
            coin_text(st).split("\n\n<i>")[0] + f"\n\nВыпало: <b>{'🦅 Орёл' if res == 'h' else '🪙 Решка'}</b>\n{verdict}",
            parse_mode="HTML")


# --- угадай число (гонка)
NUM_MAX = 12


def num_kb(st: dict) -> InlineKeyboardMarkup:
    btns = [("❌" if n in st["crossed"] else str(n), f"gg:n:{n}") for n in range(1, NUM_MAX + 1)]
    return _kb(*[btns[i:i + 4] for i in range(0, NUM_MAX, 4)])


def num_text(st: dict) -> str:
    log_ = "\n".join(st["log"][-5:])
    return (f"🔢 <b>Угадай число от 1 до {NUM_MAX}</b>\n{LINE}\n"
            "У каждого одна попытка. Кто первым попадёт, тот победил!\n" + (f"\n{log_}" if log_ else ""))


async def gg_num(q, st, action, arg):
    user = q.from_user
    if action != "n" or not arg or not arg.isdigit():
        await q.answer()
        return
    n = int(arg)
    if user.id in st["guessers"]:
        await q.answer("У вас уже была попытка, ждём других 🙂", show_alert=True)
        return
    if n in st["crossed"]:
        await q.answer("Это число уже названо")
        return
    st["guessers"].add(user.id)
    await q.answer()
    key = (q.message.chat.id, q.message.message_id)
    if n == st["secret"]:
        add_group_win(q.message.chat.id, user.id, _name(user))
        GG.pop(key, None)
        await q.message.edit_text(f"🎉 <b>{esc(_name(user))}</b> угадал(а) число <b>{n}</b>!\n{LINE}\n"
                                  "🏆 Победа записана в таблицу лидеров (/top).", parse_mode="HTML")
        return
    st["crossed"].add(n)
    st["log"].append(f"❌ {n}: {esc(_name(user))}")
    if len(st["crossed"]) >= NUM_MAX - 1:                  # остался один вариант
        GG.pop(key, None)
        await q.message.edit_text(f"😅 Никто не угадал. Это было число <b>{st['secret']}</b>.", parse_mode="HTML")
        return
    await q.message.edit_text(num_text(st), parse_mode="HTML", reply_markup=num_kb(st))


async def gg_new(q, kind: str):
    user, chat = q.from_user, q.message.chat
    name = _name(user)
    if kind == "dice":
        st = {"type": "dice", "host": user.id, "host_name": name, "throws": {}}
        m = await q.message.reply_text(dice_text(st), parse_mode="HTML", reply_markup=DICE_KB())
    elif kind == "rps":
        st = {"type": "rps", "p1": (user.id, name), "p2": None, "choices": {}}
        m = await q.message.reply_text(rps_text(st), parse_mode="HTML", reply_markup=_kb([("⚔️ Принять вызов", "gg:join")]))
    elif kind == "coin":
        st = {"type": "coin", "host": user.id, "host_name": name, "bets": {}}
        m = await q.message.reply_text(coin_text(st), parse_mode="HTML", reply_markup=COIN_KB())
    elif kind == "num":
        st = {"type": "num", "secret": random.randint(1, NUM_MAX), "crossed": set(), "guessers": set(), "log": []}
        m = await q.message.reply_text(num_text(st), parse_mode="HTML", reply_markup=num_kb(st))
    else:
        return
    gg_put((chat.id, m.message_id), st)


async def on_gg(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    chat, user = q.message.chat, q.from_user
    if chat.type == "private" or chat.id not in USERS["groups"] or user.id in USERS["blocked"]:
        await q.answer()
        return
    parts = q.data.split(":")[1:]
    action, arg = parts[0], (parts[1] if len(parts) > 1 else None)
    if action == "top":
        await q.answer()
        await q.message.reply_text(group_board(chat.id), parse_mode="HTML")
        return
    if action == "new":
        await q.answer()
        await gg_new(q, arg)
        return
    st = GG.get((chat.id, q.message.message_id))
    if st is None:
        await q.answer("Эта игра закончена или бот перезапускался. Откройте /games", show_alert=True)
        return
    await {"dice": gg_dice, "rps": gg_rps, "coin": gg_coin, "num": gg_num}[st["type"]](q, st, action, arg)


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
        await context.bot.send_message(chat.id, GROUP_HELLO, parse_mode="HTML")
        return
    GROUP_PENDING[chat.id] = f"{title} (добавил(а): {adder.full_name})"
    try:
        await context.bot.send_message(
            OWNER_ID, f"🔔 Бота добавили в группу\n{GROUP_PENDING[chat.id]}\nID чата: {chat.id}",
            reply_markup=_kb([("✅ Разрешить", f"acc:gok:{chat.id}"), ("🚪 Выйти", f"acc:gno:{chat.id}")]))
        await context.bot.send_message(chat.id, "⏳ Жду разрешения владельца бота.")
    except Exception:
        log.exception("не удалось спросить разрешение для группы")


async def m_video(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("Пришлите ссылку на видео из YouTube, TikTok или Instagram.")


async def m_file(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        "Пришлите видео или картинку, и я предложу действия:\n"
        "• видео: сжать или вытащить MP3\n"
        "• картинка: PDF, стикер или чтение QR-кода")


async def m_qr(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data["await"] = "qr"
    await update.effective_message.reply_text(
        "Пришлите текст или ссылку, и я сделаю QR-код.\n"
        "Чтобы прочитать готовый QR, пришлите его фото и нажмите «Читать QR».")


async def m_help(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await start(update, context)


def owner_only(fn):
    async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if is_owner(update.effective_user.id):
            await fn(update, context)
    return wrapper


MENU = {                                           # текст кнопки -> действие
    BTN_VIDEO: m_video, BTN_FILE: m_file, BTN_QR: m_qr,
    BTN_WEATHER: weather_cmd, BTN_HELP: m_help, BTN_GAMES: m_games, BTN_TOP: top_private,
    BTN_MORNING: morning_cmd, BTN_RAIN: rain_cmd,
    BTN_FRIENDS: owner_only(friends_cmd),
}


async def on_menu(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    uid = q.from_user.id
    if not is_allowed(uid):
        return
    if q.data == "menu:city":
        context.user_data["await"] = "city"
        await q.message.reply_text("Напишите название города, например: Казань")
    elif q.data == "menu:morning":
        on = not pref(uid, "morning")
        USERS["prefs"].setdefault(uid, {})["morning"] = on
        _save_users()
        try:
            await q.edit_message_reply_markup(reply_markup=morning_kb(uid))
        except Exception:
            pass
        await q.message.reply_text(f"Утренняя сводка в {MORNING_TIME} включена." if on
                                   else "Утренняя сводка выключена. Кнопка «☀️ Сводка» работает как раньше.")


async def post_init(app: Application):
    """Команды в меню «/», описание и подпись бота."""
    user_cmds = [BotCommand("start", "🏠 Меню"), BotCommand("weather", "🌦 Погода"), BotCommand("morning", "☀️ Сводка"),
                 BotCommand("rain", "☔ Дождь вкл/выкл"), BotCommand("qr", "🔲 Сделать QR-код"),
                 BotCommand("top", "🏆 Таблица лидеров")]
    owner_cmds = user_cmds + [BotCommand("friends", "👥 Друзья и группы"), BotCommand("add", "➕ Добавить друга по ID")]
    group_cmds = [BotCommand("games", "🎮 Игры для компании"), BotCommand("top", "🏆 Лидеры группы")]
    try:
        await app.bot.set_my_commands(user_cmds)
        await app.bot.set_my_commands(owner_cmds, scope=BotCommandScopeChat(OWNER_ID))
        await app.bot.set_my_commands(group_cmds, scope=BotCommandScopeAllGroupChats())
        await app.bot.set_my_short_description("Видео, погода, QR, игры и многое другое ✨")
        await app.bot.set_my_description(
            "Видео из TikTok, Reels и YouTube, конвертер, QR-коды, погода, утренняя сводка, "
            "оповещения о дожде и игры с таблицей лидеров. Нажмите «Начать» ✨")
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
    owner = filters.User(OWNER_ID)                           # только владелец: /morning, /rain
    allowed = filters.ChatType.PRIVATE                       # личные сообщения (доступ проверил guard)
    owner = owner & filters.ChatType.PRIVATE
    groups = filters.ChatType.GROUPS
    app.add_handler(CommandHandler(["start", "help", "menu"], start, allowed))
    app.add_handler(CommandHandler("morning", morning_cmd, allowed))
    app.add_handler(CommandHandler("weather", weather_cmd, allowed))
    app.add_handler(CommandHandler("qr", qr_cmd, allowed))
    app.add_handler(CommandHandler("rain", rain_cmd, allowed))
    app.add_handler(CommandHandler("friends", friends_cmd, owner))
    app.add_handler(CommandHandler("add", add_cmd, owner))
    app.add_handler(CommandHandler("top", top_private, allowed))
    app.add_handler(CommandHandler("games", games_cmd, groups))
    app.add_handler(CommandHandler("top", top_group_cmd, groups))
    app.add_handler(CommandHandler(["start", "help"], group_help, groups))
    app.add_handler(ChatMemberHandler(on_bot_added, ChatMemberHandler.MY_CHAT_MEMBER))
    app.add_handler(CallbackQueryHandler(on_gg, pattern=r"^gg:"))
    app.add_handler(MessageHandler(allowed & filters.TEXT & ~filters.COMMAND, on_text))
    app.add_handler(MessageHandler(allowed & (filters.VIDEO | filters.PHOTO | filters.Document.ALL), on_media))
    app.add_handler(CallbackQueryHandler(on_access, pattern=r"^acc:"))
    app.add_handler(CallbackQueryHandler(on_menu, pattern=r"^menu:"))
    app.add_handler(CallbackQueryHandler(on_game, pattern=r"^game:"))
    app.add_handler(CallbackQueryHandler(on_button, pattern=r"^(yt|conv):"))
    hh, mm = map(int, MORNING_TIME.split(":"))
    app.job_queue.run_daily(send_morning, time(hh, mm, tzinfo=TZ))
    app.job_queue.run_repeating(check_rain, interval=600, first=30)   # проверка дождя каждые 10 минут
    app.run_polling()


if __name__ == "__main__":
    main()
