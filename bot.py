"""Личный Telegram-бот: скачивание видео, конвертер, утренняя сводка."""
import asyncio
import logging
import math
import os
import re
import shutil
import tempfile
from datetime import time
from pathlib import Path
from zoneinfo import ZoneInfo

import feedparser
import httpx
import yt_dlp
from dotenv import load_dotenv
from PIL import Image
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
async def get_weather() -> str:
    async with httpx.AsyncClient(timeout=15) as c:
        geo = (await c.get("https://geocoding-api.open-meteo.com/v1/search",
                           params={"name": CITY, "count": 1, "language": "ru"})).json()
        place = geo["results"][0]
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


# ---------- хендлеры ----------
HELP = (
    "Что я умею:\n"
    "• Ссылка TikTok / Reels — пришлю видео без водяного знака\n"
    "• Ссылка YouTube — видео или MP3 на выбор\n"
    "• Видео-файл — сжать или вытащить MP3\n"
    "• Картинка — сделать PDF\n"
    f"• Каждое утро в {MORNING_TIME} — погода и новости (/morning — прямо сейчас)"
)


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(HELP)


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
        buttons = [("📄 В PDF", "conv:pdf")]
    elif msg.document and (msg.document.mime_type or "").startswith("image/"):
        context.user_data["fid"] = msg.document.file_id
        buttons = [("📄 В PDF", "conv:pdf")]
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
    app.add_handler(MessageHandler(owner & filters.TEXT & ~filters.COMMAND, on_text))
    app.add_handler(MessageHandler(owner & (filters.VIDEO | filters.PHOTO | filters.Document.ALL), on_media))
    app.add_handler(CallbackQueryHandler(on_button))
    hh, mm = map(int, MORNING_TIME.split(":"))
    app.job_queue.run_daily(send_morning, time(hh, mm, tzinfo=TZ))
    app.run_polling()


if __name__ == "__main__":
    main()
