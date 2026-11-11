"""Личный Telegram-бот: скачивание видео, конвертер, утренняя сводка."""
import asyncio
import io
import logging
import math
import os
import re
import shutil
import tempfile
import time as time_module
from datetime import time
from pathlib import Path
from zoneinfo import ZoneInfo

import feedparser
import httpx
import qrcode
import yt_dlp
from dotenv import load_dotenv
from PIL import Image, ImageOps
from telegram import InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.ext import (
    Application, CallbackQueryHandler, CommandHandler,
    ContextTypes, MessageHandler, filters,
)

load_dotenv()
BOT_TOKEN = os.environ["BOT_TOKEN"]
OWNER_ID = int(os.environ["OWNER_ID"])          # только ты можешь пользоваться ботом
CITY = os.getenv("CITY", "Москва")
MORNING_TIME = os.getenv("MORNING_TIME", "08:00")
TZ = ZoneInfo(os.getenv("TZ", "Europe/Moscow"))
LOCAL_API_URL = os.getenv("LOCAL_API_URL")       # напр. http://localhost:8081 (снимает лимит до 2 ГБ)
MAX_UPLOAD = (1900 if LOCAL_API_URL else 49) * 1024 * 1024   # макс. размер одного файла

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
logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger("bot")


# ---------- скачивание (yt-dlp) ----------
def _download(url: str, audio: bool, outdir: str) -> str:
    opts = {
        "outtmpl": f"{outdir}/%(id)s.%(ext)s",
        "noplaylist": True,
        "quiet": True,
    }
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
        return info["requested_downloads"][0]["filepath"]


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
    msg = await update.effective_message.reply_text("⏳ Скачиваю...")
    tmp = tempfile.mkdtemp()
    try:
        path = await asyncio.to_thread(_download, url, audio, tmp)
        await send_media(update, path, audio)
        await msg.delete()
    except Exception as e:
        log.exception("download failed")
        await msg.edit_text(f"❌ Не получилось: {str(e)[:300]}")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


# ---------- конвертер (ffmpeg / Pillow) ----------
async def ffmpeg(*args: str):
    proc = await asyncio.create_subprocess_exec(
        "ffmpeg", "-y", *args,
        stdout=asyncio.subprocess.DEVNULL, stderr=asyncio.subprocess.PIPE,
    )
    _, err = await proc.communicate()
    if proc.returncode != 0:
        raise RuntimeError(err.decode()[-300:])


async def convert(update: Update, context: ContextTypes.DEFAULT_TYPE, mode: str):
    fid = context.user_data.get("fid")
    if not fid:
        await update.effective_message.reply_text("Сначала пришли файл.")
        return
    msg = await update.effective_message.reply_text("⏳ Обрабатываю...")
    tmp = Path(tempfile.mkdtemp())
    try:
        src = tmp / "input"
        tg_file = await context.bot.get_file(fid)    # лимит скачивания у бота — 20 МБ
        await tg_file.download_to_drive(src)
        if mode == "pdf":
            out = tmp / "result.pdf"
            Image.open(src).convert("RGB").save(out)
            await update.effective_message.reply_document(open(out, "rb"))
        elif mode == "sticker":
            img = ImageOps.exif_transpose(Image.open(src)).convert("RGBA")
            scale = 512 / max(img.size)               # одна сторона ровно 512 px
            img = img.resize((max(1, round(img.width * scale)), max(1, round(img.height * scale))),
                             Image.LANCZOS)
            out = tmp / "sticker.webp"
            for quality in (90, 75, 60, 40):          # стикер должен быть меньше 512 КБ
                img.save(out, "WEBP", quality=quality)
                if out.stat().st_size < 500 * 1024:
                    break
            await update.effective_message.reply_sticker(open(out, "rb"))
        elif mode == "qrread":
            import cv2                                # тяжёлая библиотека, грузим только здесь
            text, _, _ = cv2.QRCodeDetector().detectAndDecode(cv2.imread(str(src)))
            await update.effective_message.reply_text(text or "QR-код на картинке не найден.")
        elif mode == "mp3":
            out = tmp / "result.mp3"
            await ffmpeg("-i", str(src), "-vn", "-acodec", "libmp3lame", "-q:a", "2", str(out))
            await update.effective_message.reply_audio(open(out, "rb"))
        elif mode == "compress":
            out = tmp / "result.mp4"
            await ffmpeg("-i", str(src), "-vf", "scale=-2:720", "-vcodec", "libx264",
                         "-crf", "28", "-preset", "veryfast", "-acodec", "aac",
                         "-b:a", "96k", str(out))
            await update.effective_message.reply_video(open(out, "rb"))
        await msg.delete()
    except Exception as e:
        log.exception("convert failed")
        await msg.edit_text(f"❌ Ошибка: {str(e)[:300]}")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


# ---------- утренняя сводка ----------
async def _geocode(c: httpx.AsyncClient) -> dict:
    geo = (await c.get("https://geocoding-api.open-meteo.com/v1/search",
                       params={"name": CITY, "count": 1, "language": "ru"})).json()
    return geo["results"][0]


async def get_forecast(hours=(2, 4, 6)) -> str:
    """Погода сейчас и через 2, 4, 6 часов."""
    async with httpx.AsyncClient(timeout=15) as c:
        place = await _geocode(c)
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


async def get_weather() -> str:
    async with httpx.AsyncClient(timeout=15) as c:
        place = await _geocode(c)
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


async def morning_text() -> str:
    try:
        weather = await get_weather()
    except Exception:
        weather = "Погоду получить не удалось."
    news = await asyncio.to_thread(_fetch_news)
    return f"☀️ <b>Доброе утро!</b>\n\n{weather}\n\n📰 <b>Главное в мире:</b>\n{news}"


async def send_morning(context: ContextTypes.DEFAULT_TYPE):
    await context.bot.send_message(OWNER_ID, await morning_text(),
                                   parse_mode="HTML", disable_web_page_preview=True)


# ---------- оповещение о дожде ----------
RAIN_MM = 0.1                    # осадков за 15 минут, с которых считаем, что дождь начался
RAIN_COOLDOWN = 90 * 60          # не чаще одного оповещения в полтора часа


async def check_rain(context: ContextTypes.DEFAULT_TYPE):
    """Раз в 10 минут смотрит прогноз на 15-минутных интервалах."""
    data = context.bot_data
    if not data.get("rain_on", True):
        return
    try:
        async with httpx.AsyncClient(timeout=15) as c:
            place = await _geocode(c)
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
        snow = [s or 0 for s in m["snowfall"]]
    except Exception:
        log.exception("rain check failed")
        return

    window = precip[idx: idx + 9]                 # текущий момент + следующие 2 часа
    if window[0] >= RAIN_MM or all(p < RAIN_MM for p in window):
        data["rain_alerted"] = False              # дождь уже идёт или не ожидается: готовимся к следующему
        return
    soon = [k for k in (1, 2) if precip[idx + k] >= RAIN_MM]   # через 15 и 30 минут
    if not soon or data.get("rain_alerted"):
        return
    if time_module.time() - data.get("rain_last", 0) < RAIN_COOLDOWN:
        return
    snowing = any(snow[idx + k] > 0 for k in soon)
    what = "пойдёт снег ❄️" if snowing else "пойдёт дождь ☔"
    await context.bot.send_message(
        OWNER_ID, f"Примерно через {soon[0] * 15} мин в {place['name']} {what}")
    data["rain_alerted"] = True
    data["rain_last"] = time_module.time()


async def rain_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    on = not context.bot_data.get("rain_on", True)
    context.bot_data["rain_on"] = on
    await update.message.reply_text(
        "☔ Оповещения о дожде включены." if on else "Оповещения о дожде выключены.")


# ---------- QR-коды ----------
async def qr_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    parts = (update.message.text or "").split(maxsplit=1)
    if len(parts) < 2 or not parts[1].strip():
        await update.message.reply_text("Напишите так: /qr https://example.com")
        return
    try:
        qr = qrcode.QRCode(box_size=12, border=4)
        qr.add_data(parts[1].strip())
        qr.make(fit=True)
        buf = io.BytesIO()
        qr.make_image(fill_color="black", back_color="white").save(buf, "PNG")
        buf.seek(0)
        await update.message.reply_photo(buf)
    except Exception:
        log.exception("qr failed")
        await update.message.reply_text("Не получилось: текст слишком длинный для QR-кода.")


# ---------- хендлеры ----------
HELP = (
    "Что я умею:\n"
    "• Ссылка TikTok / Reels — пришлю видео без водяного знака\n"
    "• Ссылка YouTube — видео или MP3 на выбор\n"
    "• Видео-файл — сжать или вытащить MP3\n"
    "• Картинка — PDF, стикер или чтение QR-кода\n"
    "• /qr текст или ссылка — сделать QR-код\n"
    "• /weather — погода сейчас и через 2, 4 и 6 часов\n"
    "• /rain — включить или выключить оповещения о дожде (включены по умолчанию)\n"
    f"• Каждое утро в {MORNING_TIME} — погода и новости (/morning — прямо сейчас)"
)


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(HELP)


async def weather_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    try:
        text = await get_forecast()
    except Exception:
        log.exception("forecast failed")
        text = "Не удалось получить прогноз, попробуйте позже."
    await update.message.reply_text(text)


async def morning_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(await morning_text(), parse_mode="HTML",
                                    disable_web_page_preview=True)


async def on_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    m = URL_RE.search(update.message.text or "")
    if not m:
        await update.message.reply_text("Пришли ссылку или файл. /help — список функций.")
        return
    url = m.group(0)
    if "youtube.com" in url or "youtu.be" in url:
        context.user_data["url"] = url
        kb = InlineKeyboardMarkup([[
            InlineKeyboardButton("🎬 Видео", callback_data="yt:video"),
            InlineKeyboardButton("🎵 MP3", callback_data="yt:audio"),
        ]])
        await update.message.reply_text("Что скачать?", reply_markup=kb)
    else:                                         # TikTok, Instagram и всё остальное
        await download_and_send(update, url)


async def on_media(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg = update.message
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
    kind, action = q.data.split(":")
    if kind == "yt":
        url = context.user_data.get("url")
        if url:
            await download_and_send(update, url, audio=(action == "audio"))
    else:
        await convert(update, context, action)


def main():
    builder = (Application.builder().token(BOT_TOKEN)
               .concurrent_updates(True)             # долгая загрузка не блокирует остальные команды
               .read_timeout(1800).write_timeout(1800).connect_timeout(60))
    if LOCAL_API_URL:
        builder = (builder.base_url(f"{LOCAL_API_URL}/bot")
                   .base_file_url(f"{LOCAL_API_URL}/file/bot")
                   .local_mode(True))
    app = builder.build()
    owner = filters.User(OWNER_ID)
    app.add_handler(CommandHandler(["start", "help"], start, owner))
    app.add_handler(CommandHandler("morning", morning_cmd, owner))
    app.add_handler(CommandHandler("weather", weather_cmd, owner))
    app.add_handler(CommandHandler("qr", qr_cmd, owner))
    app.add_handler(CommandHandler("rain", rain_cmd, owner))
    app.add_handler(MessageHandler(owner & filters.TEXT & ~filters.COMMAND, on_text))
    app.add_handler(MessageHandler(owner & (filters.VIDEO | filters.PHOTO | filters.Document.ALL), on_media))
    app.add_handler(CallbackQueryHandler(on_button))
    hh, mm = map(int, MORNING_TIME.split(":"))
    app.job_queue.run_daily(send_morning, time(hh, mm, tzinfo=TZ))
    app.job_queue.run_repeating(check_rain, interval=600, first=30)   # проверка дождя каждые 10 минут
    app.run_polling()


if __name__ == "__main__":
    main()
