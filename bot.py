import os
import re
import logging
import tempfile
import base64
import json
import pycountry
import requests
import time
import socket
import concurrent.futures
import asyncio
import random
import gzip
import io
from urllib.parse import urlparse
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import (
    Application,
    CommandHandler,
    MessageHandler,
    filters,
    CallbackContext,
    ConversationHandler,
    CallbackQueryHandler
)
from openai import OpenAI
import maxminddb

# Конфигурация
TOKEN = os.getenv("TELEGRAM_BOT_TOKEN")
NEURAL_API_KEY = os.getenv("NEURAL_API_KEY")
MAX_FILE_SIZE = 15 * 1024 * 1024
MAX_MSG_LENGTH = 4000
MAX_WORKERS = 15
MAX_GEO_WORKERS = 5
CHUNK_SIZE = 100
NEURAL_MODEL = "deepseek/deepseek-r1-0528"
NEURAL_TIMEOUT = 15
MAX_RETRIES = 8
SUPPORTED_PROTOCOLS = {
    'vmess', 'vless', 'trojan', 'ss', 'ssr', 'socks', 'http', 
    'https', 'hysteria', 'hysteria2', 'wg', 'openvpn', 'brook'
}

# URL для скачивания базы геолокации
DB_IP_URL = "https://download.db-ip.com/free/dbip-country-lite-2024-06.mmdb.gz"
DB_IP_FILENAME = "dbip-country-lite.mmdb"

# Состояния диалога
(START, WAITING_FILE, WAITING_COUNTRY, WAITING_MODE, 
 WAITING_NUMBER, SENDING_CONFIGS, PROCESSING_STRICT) = range(7)

# Настройка логирования
logging.basicConfig(
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    level=logging.INFO
)
logger = logging.getLogger(__name__)

# Инициализация нейросети
neural_client = None
if NEURAL_API_KEY:
    neural_client = OpenAI(
        base_url="https://api.novita.ai/v3/openai",
        api_key=NEURAL_API_KEY,
        timeout=NEURAL_TIMEOUT
    )
    logger.info("Нейросеть DeepSeek-R1 инициализирована")
else:
    logger.warning("NEURAL_API_KEY не установлен, функции нейросети отключены")

# Кэширование
country_cache = {}
geo_cache = {}
dns_cache = {}
config_cache = {}
instruction_cache = {}
country_normalization_cache = {}
neural_improvement_cache = {}
protocol_cache = {}

# Инициализация базы геолокации
geoip_reader = None

async def initialize_geoip_database():
    """Инициализация базы геолокации при запуске"""
    global geoip_reader
    
    try:
        # Скачивание базы данных
        logger.info(f"Скачивание базы геолокации: {DB_IP_URL}")
        response = requests.get(DB_IP_URL, timeout=60)
        response.raise_for_status()
        
        # Распаковка и загрузка в память
        with gzip.GzipFile(fileobj=io.BytesIO(response.content)) as gz_file:
            db_content = gz_file.read()
        
        # Используем BytesIO для работы с данными в памяти
        buffer = io.BytesIO(db_content)
        geoip_reader = maxminddb.open_database(
            buffer, 
            maxminddb.MODE_MEMORY
        )
        
        logger.info("База геолокации успешно загружена в память")
        return True
    except Exception as e:
        logger.error(f"Ошибка инициализации базы геолокации: {e}")
        return False

def clear_temporary_data(context: CallbackContext):
    """Очистка временных данных в user_data"""
    keys_to_clear = [
        'matched_configs', 'current_index', 'stop_sending', 
        'strict_in_progress', 'improved_search', 'country_request', 
        'country', 'target_country', 'country_codes', 'search_mode',
        'file_path', 'file_paths'
    ]
    for key in keys_to_clear:
        if key in context.user_data:
            del context.user_data[key]

def normalize_text(text: str) -> str:
    """Нормализация текста страны для поиска"""
    text = text.lower().strip()
    
    if text in country_normalization_cache:
        return country_normalization_cache[text]
    
    ru_en_map = {
        "россия": "russia", "русский": "russia", "рф": "russia", "ру": "russia",
        "сша": "united states", "америка": "united states", "usa": "united states", 
        "us": "united states", "соединенные штаты": "united states", "соединённые штаты": "united states",
        "германия": "germany", "дойчланд": "germany", "deutschland": "germany", "де": "germany",
        "япония": "japan", "японии": "japan", "jp": "japan", "яп": "japan",
        "франция": "france", "фр": "france", "франс": "france",
        "великобритания": "united kingdom", "брит": "united kingdom", "англия": "united kingdom", 
        "gb": "united kingdom", "uk": "united kingdom", "гб": "united kingdom",
        "сингапур": "singapore", "sg": "singapore", "синг": "singapore",
        "нидерланды": "netherlands", "голландия": "netherlands", "nl": "netherlands", "нл": "netherlands",
        "канада": "canada", "ca": "canada", "кан": "canada",
        "швейцария": "switzerland", "ch": "switzerland", "швейц": "switzerland",
        "швеция": "sweden", "se": "sweden", "швед": "sweden",
        "австралия": "australia", "оз": "australia", "au": "australia", "австр": "australia",
        "бразилия": "brazil", "br": "brazil", "браз": "brazil",
        "индия": "india", "in": "india", "инд": "india",
        "южная корея": "south korea", "кр": "south korea", "sk": "south korea", 
        "корея": "south korea", "кор": "south korea",
        " турция": "turkey", "tr": "turkey", " тур ": "turkey",
        "тайвань": "taiwan", "tw": "taiwan", "тайв": "taiwan",
        "юар": "south africa", "sa": "south africa", "африка": "south africa",
        "оаэ": "united arab emirates", "эмираты": "united arab emirates", 
        "uae": "united arab emirates", "арабские": "united arab emirates",
        "саудовская аравия": "saudi arabia", "сауд": "saudi arabia", 
        "ksa": "saudi arabia", "саудовская": "saudi arabia",
        "израиль": "israel", "il": "israel", "изр": "israel",
        "мексика": "mexico", "mx": "mexico", "мекс": "mexico",
        "аргентина": "argentina", "ar": "argentina", "арг": "argentina",
        "италия": "italy", "it": "italy", "ит": "italy",
        "испания": "spain", "es": "spain", "исп": "spain",
        "португалия": "portugal", "pt": "portugal", "порт": "portugal",
        "норвегия": "norway", "no": "norway", "норв": "norway",
        "финляндия": "finland", "fi": "finland", "фин": "finland",
        "дания": "denmark", "dk": "denmark", "дан": "denmark",
        "польша": "poland", "pl": "poland", "пол": "poland",
        "украина": "ukraine", "ua": "ukraine", "укр": "ukraine",
        "беларусь": "belarus", "by": "belarus", "бел": "belarus",
        "китай": "china", "cn": "china", "кнр": "china",
        "индонезия": "indonesia", "id": "indonesia", "индо": "indonesia",
        "малайзия": "malaysia", "my": "malaysia", "малай": "malaysia",
        "филиппины": "philippines", "ph": "philippines", "фил": "philippines",
        "вьетнам": "vietnam", "vn": "vietnam", "вьет": "vietnam",
        "тайланд": "thailand", "th": "thailand", "тай": "thailand",
        "чехия": "czech republic", "cz": "czech republic", "чех": "czech republic",
        "румыния": "romania", "ro": "romania", "рум": "romania",
        "венгрия": "hungary", "hu": "hungary", "венг": "hungary",
        "греция": "greece", "gr": "greece", "грец": "greece",
        "болгария": "bulgaria", "bg": "bulgaria", "болг": "bulgaria",
        "египет": "egypt", "eg": "egypt", "егип": "egypt",
        "нигерия": "nigeria", "ng": "nigeria", "нигер": "nigeria",
        "кения": "kenya", "ke": "kenya", "кен": "kenya",
        "колумбия": "colombia", "co": "colombia", "колумб": "colombia",
        "перу": "peru", "pe": "peru",
        "чили": "chile", "cl": "chile",
        "венесуэла": "venezuela", "ve": "venezuela", "венес": "venezuela",
        "австрия": "austria", "at": "austria", "австр": "austria",
        "бельгия": "belgium", "be": "belgium", "бельг": "belgium",
        "ирландия": "ireland", "ie": "ireland", "ирл": "ireland",
        "алжир": "algeria", "dz": "algeria", "алж": "algeria",
        "ангола": "angola", "ao": "angola", "анг": "angola",
        "бангладеш": "bangladesh", "bd": "bangladesh", "банг": "bangladesh",
        "камбоджа": "cambodia", "kh": "cambodia", "камб": "cambodia",
        "коста-рика": "costa rica", "cr": "costa rica", "коста": "costa rica",
        "хорватия": "croatia", "hr": "croatia", "хорв": "croatia",
        "куба": "cuba", "cu": "cuba",
        "эстония": "estonia", "ee": "estonia", "эст": "estonia",
        "грузия": "georgia", "ge": "georgia", "груз": "georgia",
        "гана": "ghana", "gh": "ghana",
        "иран": "iran", "ir": "iran",
        "иордания": "jordan", "jo": "jordan", "иорд": "jordan",
        "казахстан": "kazakhstan", "kz": "kazakhstan", "каз": "kazakhstan",
        "кувейт": "kuwait", "kw": "kuwait", "кув": "kuwait",
        "ливан": "lebanon", "lb": "lebanon", "либ": "lebanon",
        "ливия": "libya", "ly": "libya",
        "марокко": "morocco", "ma": "morocco", "мар": "morocco",
        "непал": "nepal", "np": "nepal",
        "оман": "oman", "om": "oman",
        "пакистан": "pakistan", "pk": "pakistan", "пак": "pakistan",
        "катар": "qatar", "qa": "qatar", "кат": "qatar",
        "сербия": "serbia", "rs": "serbia", "серб": "serbia",
        "словакия": "slovakia", "sk": "slovakia", "словак": "slovakia",
        "словения": "slovenia", "si": "slovenia", "словен": "slovenia",
        "судан": "sudan", "sd": "sudan",
        "сирия": "syria", "sy": "syria",
        "тунис": "tunisia", "tn": "tunisia", "тун": "tunisia",
        "уругвай": "uruguay", "uy": "uruguay", "уруг": "uruguay",
        "узбекистан": "uzbekistan", "uz": "uzbekistan", "узб": "uzbekistan",
        "йемен": "yemen", "ye": "yemen"
    }
    for key, value in ru_en_map.items():
        text = text.replace(key, value)
    return text

async def neural_normalize_country(text: str) -> str:
    """Нормализация страны с помощью нейросети"""
    if not neural_client:
        return None
    
    if text in country_cache:
        return country_cache[text]
    
    system_prompt = (
        "Определи страну по тексту. Верни только английское название страны в нижнем регистре. "
        "Примеры: 'рф' → 'russia', 'соединенные штаты' → 'united states'. "
        "Если не уверен, верни None."
    )
    try:
        response = neural_client.chat.completions.create(
            model=NEURAL_MODEL,
            messages=[
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": text}
            ],
            max_tokens=50,
            temperature=0.1
        )
        result = response.choices[0].message.content.strip().lower()
        if result and len(result) < 50:
            try:
                country = pycountry.countries.search_fuzzy(result)[0]
                country_name = country.name.lower()
                country_cache[text] = country_name
                return country_name
            except:
                return result
        return None
    except Exception as e:
        logger.error(f"Ошибка нейросети: {e}")
        return None

async def neural_detect_country(config: str) -> str:
    """Определение страны конфига с помощью нейросети"""
    if not neural_client:
        return None
    
    config_hash = hash(config)
    if config_hash in config_cache:
        return config_cache[config_hash]
    
    system_prompt = (
        "Определи страну для этого VPN конфига. Ответь только названием страны на английском в нижнем регистре "
        "или 'unknown', если не удалось определить. Учитывай явные указания страны в названии сервера или комментариях."
    )
    try:
        response = neural_client.chat.completions.create(
            model=NEURAL_MODEL,
            messages=[
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": config}
            ],
            max_tokens=20,
            temperature=0.1
        )
        result = response.choices[0].message.content.strip().lower()
        result = re.sub(r'[^a-z\s]', '', result)
        if 'unknown' in result:
            return None
        
        config_cache[config_hash] = result
        return result
    except Exception as e:
        logger.error(f"Ошибка нейросети при определении страны конфига: {e}")
        return None

async def generate_country_instructions(country: str) -> str:
    """Генерация инструкций для страны с помощью нейросети"""
    if not neural_client:
        return "Инструкции недоступны ( нейросеть отключена)"
    
    if country in instruction_cache:
        return instruction_cache[country]
    
    system_prompt = (
        f"Ты эксперт по VPN. Сгенерируй краткую инструкцию по использованию VPN для пользователей из {country}. "
        "Инструкция должна быть на русском, понятной и содержать основные шаги. "
        "Максимум 300 символов."
    )
    try:
        response = neural_client.chat.completions.create(
            model=NEURAL_MODEL,
            messages=[
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": f"Сгенерируй инструкцию для {country}"}
            ],
            max_tokens=300,
            temperature=0.7
        )
        instructions = response.choices[0].message.content.strip()
        instruction_cache[country] = instructions
        return instructions
    except Exception as e:
        logger.error(f"Ошибка генерации инструкций: {e}")
        return f"⚠️ Не удалось сгенерировать инструкцию для {country}"

async def neural_improve_search(country: str) -> dict:
    """Улучшение поиска с помощью нейросети"""
    if not neural_client:
        return None
    
    if country in neural_improvement_cache:
        return neural_improvement_cache[country]
    
    system_prompt = (
        "Ты — поисковый агент для бота VPN. Сгенерируй улучшенные инструкции для поиска конфигов в указанной стране. "
        "Верни JSON объект с полями: "
        "'keywords' (дополнительные ключевые слова для поиска), "
        "'patterns' (регулярные выражения для идентификации страны в конфигах). "
        "Пример: {'keywords': ['jp', 'japan', 'tokyo'], 'patterns': [r'\\.jp\\b', r'japan']}"
    )
    try:
        response = neural_client.chat.completions.create(
            model=NEURAL_MODEL,
            messages=[
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": country}
            ],
            response_format={"type": "json_object"},
            max_tokens=200,
            temperature=0.3
        )
        result = response.choices[0].message.content.strip()
        improvement = json.loads(result)
        neural_improvement_cache[country] = improvement
        return improvement
    except Exception as e:
        logger.error(f"Ошибка улучшения поиска: {e}")
        return None

async def start_check(update: Update, context: CallbackContext):
    """Начало проверки конфигов с выбором действия"""
    clear_temporary_data(context)
    user_id = update.message.from_user.id
    
    if 'configs' in context.user_data and context.user_data['configs'] and 'last_country' in context.user_data:
        keyboard = [
            [InlineKeyboardButton("🌍 Использовать текущий файл", callback_data='use_current_file')],
            [InlineKeyboardButton("📤 Загрузить новый файл", callback_data='new_file')],
            [InlineKeyboardButton("❌ Отменить", callback_data='cancel')]
        ]
        reply_markup = InlineKeyboardMarkup(keyboard)
        
        await update.message.reply_text(
            "У вас уже есть загруженный файл конфигов. Хотите использовать его или загрузить новый?",
            reply_markup=reply_markup
        )
        return START
    else:
        await update.message.reply_text("📎 Пожалуйста, загрузите текстовый файл с конфигурациями VPN (до 15 МБ).")
        return WAITING_FILE

async def handle_document(update: Update, context: CallbackContext):
    """Обработка загруженного файла"""
    user = update.message.from_user
    document = update.message.document
    
    if not document.mime_type.startswith('text/'):
        await update.message.reply_text("❌ Пожалуйста, загрузите текстовый файл.")
        return ConversationHandler.END
    
    if document.file_size > MAX_FILE_SIZE:
        await update.message.reply_text(
            f"❌ Файл слишком большой. Максимальный размер: {MAX_FILE_SIZE//1024//1024}MB"
        )
        return ConversationHandler.END
    
    file = await context.bot.get_file(document.file_id)
    with tempfile.NamedTemporaryFile(delete=False) as tmp_file:
        await file.download_to_memory(tmp_file)
        tmp_file.seek(0)
        content = tmp_file.read().decode('utf-8', errors='replace')
        
        # Обработка многострочных конфигов
        configs = []
        current_config = []
        for line in content.splitlines():
            stripped = line.strip()
            if stripped:
                # Проверка на начало нового конфига
                if any(stripped.startswith(proto + "://") for proto in SUPPORTED_PROTOCOLS):
                    if current_config:
                        configs.append("\n".join(current_config))
                        current_config = []
                current_config.append(stripped)
        
        # Добавляем последний конфиг
        if current_config:
            configs.append("\n".join(current_config))
        
        context.user_data['configs'] = configs
        context.user_data['file_name'] = document.file_name
        tmp_file_path = tmp_file.name
    
    if os.path.exists(tmp_file_path):
        os.unlink(tmp_file_path)
    
    logger.info(f"Пользователь {user.id} загрузил файл: {document.file_name} ({len(configs)} конфигов)")
    
    keyboard = [
        [InlineKeyboardButton("📤 Загрузить еще файл", callback_data='add_file')],
        [InlineKeyboardButton("🌍 Указать страну", callback_data='set_country')]
    ]
    reply_markup = InlineKeyboardMarkup(keyboard)
    
    await update.message.reply_text(
        f"✅ Файл '{document.file_name}' успешно загружен ({len(configs)} конфигов). Вы можете:",
        reply_markup=reply_markup
    )
    return WAITING_COUNTRY

async def button_handler(update: Update, context: CallbackContext) -> int:
    """Обработчик inline кнопок"""
    query = update.callback_query
    await query.answer()
    
    if query.data == 'add_file':
        await query.edit_message_text("📎 Пожалуйста, загрузите дополнительный файл с конфигурациями.")
        return WAITING_FILE
    
    elif query.data == 'set_country':
        await query.edit_message_text("🌍 Введите название страны (на русском или английском):")
        return WAITING_COUNTRY
    
    elif query.data == 'use_current_file':
        await query.edit_message_text("🌍 Введите название страны (на русском или английском):")
        return WAITING_COUNTRY
    
    elif query.data == 'new_file':
        await query.edit_message_text("📎 Пожалуйста, загрузите текстовый файл с конфигурациями.")
        return WAITING_FILE
    
    elif query.data == 'fast_mode':
        context.user_data['search_mode'] = 'fast'
        await query.edit_message_text("⚡ Запускаю быстрый поиск...")
        await fast_search(update, context)
        return WAITING_NUMBER
    
    elif query.data == 'strict_mode':
        context.user_data['search_mode'] = 'strict'
        await query.edit_message_text("🔍 Запускаю строгий поиск...")
        await strict_search(update, context)
        return WAITING_NUMBER
    
    elif query.data == 'stop_sending':
        context.user_data['stop_sending'] = True
        await query.edit_message_text("⏹ Отправка конфигов остановлена.")
        return ConversationHandler.END
    
    elif query.data == 'stop_strict_search':
        context.user_data['stop_strict_search'] = True
        await query.edit_message_text("⏹ Строгий поиск остановлен.")
        return ConversationHandler.END
    
    elif query.data == 'cancel':
        await cancel(update, context)
        return ConversationHandler.END
    
    return context.user_data.get('current_state', WAITING_COUNTRY)

async def start_choice(update: Update, context: CallbackContext) -> int:
    return await button_handler(update, context)

async def handle_country(update: Update, context: CallbackContext):
    """Обработка ввода страны"""
    country_request = update.message.text
    context.user_data['country_request'] = country_request
    normalized_text = normalize_text(country_request)
    
    logger.info(f"Нормализованный текст: {normalized_text}")
    country = None
    found_by_neural = False
    
    try:
        countries = pycountry.countries.search_fuzzy(normalized_text)
        country = countries[0]
        logger.info(f"Pycountry определил страну: {country.name}")
    except LookupError:
        logger.info("Pycountry не смог определить страну. Пробуем нейросеть...")
        neural_country = await neural_normalize_country(normalized_text)
        if neural_country:
            try:
                countries = pycountry.countries.search_fuzzy(neural_country)
                country = countries[0]
                found_by_neural = True
                logger.info(f"Нейросеть определила страну: {country.name}")
                country_normalization_cache[country_request] = neural_country
                if normalized_text != country_request:
                    country_normalization_cache[normalized_text] = neural_country
            except:
                logger.warning("Нейросеть не смогла определить страну")
    
    if not country:
        logger.warning(f"Страна не распознана: {country_request}")
        
        if neural_client:
            try:
                improved_search = await neural_improve_search(country_request)
                if improved_search:
                    keywords = improved_search.get('keywords', [])
                    patterns = improved_search.get('patterns', [])
                    logger.info(f"Улучшенный поиск: keywords={keywords}, patterns={patterns}")
                    
                    context.user_data['improved_search'] = {
                        'keywords': keywords,
                        'patterns': patterns
                    }
                    
                    await update.message.reply_text(
                        f"🔍 Нейросеть улучшила поиск для '{country_request}'. Попробуйте снова."
                    )
                    return WAITING_COUNTRY
            except Exception as e:
                logger.error(f"Ошибка улучшения поиска: {e}")
        
        await update.message.reply_text("❌ Страна не распознана. Пожалуйста, уточните название.")
        return WAITING_COUNTRY

    context.user_data['country'] = country.name
    context.user_data['target_country'] = country.name.lower()
    context.user_data['country_codes'] = [c.alpha_2.lower() for c in countries] + [country.alpha_2.lower()]
    
    keyboard = [
        [
            InlineKeyboardButton("⚡ Быстрый поиск", callback_data='fast_mode'),
            InlineKeyboardButton("🔍 Строгий поиск", callback_data='strict_mode')
        ]
    ]
    reply_markup = InlineKeyboardMarkup(keyboard)
    
    if country.name.lower() not in instruction_cache:
        instructions = await generate_country_instructions(country.name)
        instruction_cache[country.name.lower()] = instructions
    
    await update.message.reply_text(
        f"🌍 Вы выбрали страну: {country.name}\n"
        f"ℹ️ {instruction_cache.get(country.name.lower(), 'Инструкция генерируется...')}\n\n"
        "Выберите режим поиска:",
        reply_markup=reply_markup
    )
    return WAITING_MODE

async def fast_search(update: Update, context: CallbackContext):
    """Быстрый поиск конфигов"""
    user_id = update.callback_query.from_user.id if update.callback_query else update.message.from_user.id
    configs = context.user_data.get('configs', [])
    target_country = context.user_data.get('target_country', '')
    
    if not configs or not target_country:
        await context.bot.send_message(chat_id=user_id, text="❌ Ошибка: данные для поиска отсутствуют.")
        return ConversationHandler.END
    
    start_time = time.time()
    matched_configs = []
    progress_msg = await context.bot.send_message(chat_id=user_id, text="🔎 Начинаю быстрый поиск...")
    
    improved_search = context.user_data.get('improved_search', {})
    additional_keywords = improved_search.get('keywords', [])
    additional_patterns = improved_search.get('patterns', [])
    
    total_configs = len(configs)
    for i, config in enumerate(configs):
        try:
            if is_config_relevant(
                config, 
                target_country, 
                context.user_data['country_codes'],
                additional_keywords,
                additional_patterns
            ):
                matched_configs.append(config)
        except Exception as e:
            logger.error(f"Ошибка проверки конфига #{i}: {e}")
        
        if i % 500 == 0 or i == total_configs - 1:
            progress = min((i + 1) / total_configs * 100, 100)
            progress_bar = create_progress_bar(progress)
            await context.bot.edit_message_text(
                chat_id=user_id,
                message_id=progress_msg.message_id,
                text=f"🔎 Быстрый поиск: {progress_bar} {progress:.1f}%\nОбработано: {i+1}/{total_configs}"
            )
    
    logger.info(f"Найдено {len(matched_configs)} конфигов для {context.user_data['country']}, обработка заняла {time.time()-start_time:.2f} сек")
    
    if not matched_configs:
        await context.bot.edit_message_text(
            chat_id=user_id,
            message_id=progress_msg.message_id,
            text=f"❌ Конфигурации для {context.user_data['country']} не найдены."
        )
        return ConversationHandler.END
    
    context.user_data['matched_configs'] = matched_configs
    
    await context.bot.edit_message_text(
        chat_id=user_id,
        message_id=progress_msg.message_id,
        text=f"✅ Найдено {len(matched_configs)} конфигов для {context.user_data['country']}!"
    )
    
    await context.bot.send_message(
        chat_id=user_id,
        text=f"🌍 Для страны {context.user_data['country']} найдено {len(matched_configs)} конфигов. Сколько конфигов прислать? (введите число от 1 до {len(matched_configs)})"
    )
    return WAITING_NUMBER

def get_country_for_host(host: str) -> str:
    """Получение страны для хоста"""
    ip = resolve_dns(host)
    if not ip:
        return None
    return geolocate_ip(ip)

async def strict_search(update: Update, context: CallbackContext):
    """Строгий поиск конфигов с проверкой геолокации"""
    user_id = update.callback_query.from_user.id if update.callback_query else update.message.from_user.id
    configs = context.user_data.get('configs', [])
    target_country = context.user_data.get('target_country', '')
    
    if not configs or not target_country:
        await context.bot.send_message(chat_id=user_id, text="❌ Ошибка: данные для поиска отсутствуют.")
        return ConversationHandler.END
    
    if not geoip_reader:
        await context.bot.send_message(chat_id=user_id, text="❌ База геолокации не загружена. Строгий поиск недоступен.")
        return ConversationHandler.END
    
    start_time = time.time()
    prelim_configs = []
    progress_msg = await context.bot.send_message(chat_id=user_id, text="🔎 Этап 1: предварительная фильтрация...")
    
    improved_search = context.user_data.get('improved_search', {})
    additional_keywords = improved_search.get('keywords', [])
    additional_patterns = improved_search.get('patterns', [])
    
    total_configs = len(configs)
    for i, config in enumerate(configs):
        try:
            if is_config_relevant(
                config, 
                target_country, 
                context.user_data['country_codes'],
                additional_keywords,
                additional_patterns
            ):
                prelim_configs.append(config)
        except Exception as e:
            logger.error(f"Ошибка проверки конфига #{i}: {e}")
        
        if i % 500 == 0 or i == total_configs - 1:
            progress = min((i + 1) / total_configs * 100, 100)
            progress_bar = create_progress_bar(progress)
            await context.bot.edit_message_text(
                chat_id=user_id,
                message_id=progress_msg.message_id,
                text=f"🔎 Этап 1: {progress_bar} {progress:.1f}%\nОбработано: {i+1}/{total_configs}"
            )
    
    logger.info(f"Предварительно найдено {len(prelim_configs)} конфигов, обработка заняла {time.time()-start_time:.2f} сек")
    
    if not prelim_configs:
        await context.bot.edit_message_text(
            chat_id=user_id,
            message_id=progress_msg.message_id,
            text=f"❌ Конфигурации для {context.user_data['country']} не найдены."
        )
        return ConversationHandler.END
    
    # Группировка конфигов по хостам
    host_to_configs = {}
    configs_without_host = 0
    for config in prelim_configs:
        host = extract_host(config)
        if host:
            if host not in host_to_configs:
                host_to_configs[host] = []
            host_to_configs[host].append(config)
        else:
            configs_without_host += 1

    unique_hosts = list(host_to_configs.keys())
    total_hosts = len(unique_hosts)

    logger.info(f"Уникальных хостов: {total_hosts}, конфигов без хоста: {configs_without_host}")

    if not unique_hosts:
        await context.bot.edit_message_text(
            chat_id=user_id,
            message_id=progress_msg.message_id,
            text="❌ Не удалось извлечь хосты из конфигов."
        )
        return ConversationHandler.END

    stop_keyboard = [[InlineKeyboardButton("⏹ Остановить строгий поиск", callback_data='stop_strict_search')]]
    stop_reply_markup = InlineKeyboardMarkup(stop_keyboard)

    await context.bot.edit_message_text(
        chat_id=user_id,
        message_id=progress_msg.message_id,
        text=f"🌐 Начинаю проверку геолокации для {total_hosts} уникальных хостов...",
        reply_markup=stop_reply_markup
    )

    context.user_data['strict_in_progress'] = True
    host_country_map = {}
    total_processed = 0

    # Проверка геолокации для уникальных хостов
    for host in unique_hosts:
        if context.user_data.get('stop_strict_search'):
            break
            
        ip = resolve_dns(host)
        if ip:
            country = geolocate_ip(ip)
            host_country_map[host] = country
        else:
            host_country_map[host] = None
            
        total_processed += 1
        
        # Обновление прогресса
        if total_processed % 10 == 0 or total_processed == total_hosts:
            progress = total_processed / total_hosts * 100
            progress_bar = create_progress_bar(progress)
            await context.bot.edit_message_text(
                chat_id=user_id,
                message_id=progress_msg.message_id,
                text=f"🌐 Этап 2: {progress_bar} {progress:.1f}%\nОбработано хостов: {total_processed}/{total_hosts}",
                reply_markup=stop_reply_markup
            )

    context.user_data['strict_in_progress'] = False

    # Сбор валидных конфигов
    valid_configs = []
    for host in unique_hosts:
        country = host_country_map.get(host)
        if country and country.lower() == target_country.lower():
            valid_configs.extend(host_to_configs[host])

    total_time = time.time() - start_time
    logger.info(f"Строгая проверка завершена: найдено {len(valid_configs)} конфигов, заняло {total_time:.2f} сек")
    
    if context.user_data.get('stop_strict_search'):
        await context.bot.edit_message_text(
            chat_id=user_id,
            message_id=progress_msg.message_id,
            text=f"⏹ Строгий поиск остановлен. Найдено {len(valid_configs)} конфигов."
        )
    else:
        await context.bot.edit_message_text(
            chat_id=user_id,
            message_id=progress_msg.message_id,
            text=f"✅ Строгий поиск завершен. Найдено {len(valid_configs)} конфигов."
        )
    
    if not valid_configs:
        await context.bot.send_message(chat_id=user_id, text="❌ Конфигурации не найдены.")
        return ConversationHandler.END
    
    context.user_data['matched_configs'] = valid_configs
    
    await context.bot.send_message(
        chat_id=user_id,
        text=f"🌍 Для страны {context.user_data['country']} найдено {len(valid_configs)} валидных конфигов! Сколько конфигов прислать? (введите число от 1 до {len(valid_configs)})"
    )
    return WAITING_NUMBER

async def handle_number(update: Update, context: CallbackContext):
    """Обработка ввода количества конфигов"""
    user_input = update.message.text
    user_id = update.message.from_user.id
    
    try:
        num = int(user_input)
        matched_configs = context.user_data.get('matched_configs', [])
        total = len(matched_configs)
        
        if num < 1:
            num = 1
        if num > total:
            num = total
        
        random.shuffle(matched_configs)
        selected_configs = matched_configs[:num]
        
        context.user_data['matched_configs'] = selected_configs
        context.user_data['current_index'] = 0
        context.user_data['stop_sending'] = False
        
        await update.message.reply_text(f"⏫ Начинаю отправку {num} конфигов...")
        await send_configs(update, context)
        return SENDING_CONFIGS
    except ValueError:
        await update.message.reply_text("❌ Пожалуйста, введите число.")
        return WAITING_NUMBER

async def send_configs(update: Update, context: CallbackContext):
    """Отправка конфигов пользователю"""
    user_id = update.message.from_user.id
    matched_configs = context.user_data.get('matched_configs', [])
    country_name = context.user_data.get('country', '')
    stop_sending = context.user_data.get('stop_sending', False)
    
    if not matched_configs:
        await context.bot.send_message(chat_id=user_id, text="❌ Нет конфигов для отправки.")
        return ConversationHandler.END
    
    if stop_sending:
        await context.bot.send_message(chat_id=user_id, text="⏹ Отправка остановлена.")
        return ConversationHandler.END
    
    header = f"Конфиги для {country_name}:\n\n"
    current_message = header
    messages = []
    
    for config in matched_configs:
        config_line = f"{config}\n\n"
        
        if len(current_message) + len(config_line) > MAX_MSG_LENGTH:
            messages.append(current_message)
            current_message = config_line
        else:
            current_message += config_line
    
    if current_message:
        messages.append(current_message)
    
    total_messages = len(messages)
    for i, message in enumerate(messages):
        if context.user_data.get('stop_sending'):
            await context.bot.send_message(chat_id=user_id, text="⏹ Отправка остановлена.")
            return ConversationHandler.END
        
        try:
            if i == total_messages - 1:
                progress = f"\n\n⌛ Отправлено {i+1}/{total_messages} сообщений"
                if len(message) + len(progress) <= MAX_MSG_LENGTH:
                    message += progress
            
            await context.bot.send_message(
                chat_id=user_id,
                text=f"<pre>{message}</pre>",
                parse_mode='HTML'
            )
            await asyncio.sleep(0.3)
        except Exception as e:
            logger.error(f"Ошибка отправки сообщения: {e}")
    
    await context.bot.send_message(chat_id=user_id, text="✅ Все конфиги отправлены.")
    
    context.user_data['last_country'] = context.user_data['country']
    clear_temporary_data(context)
    return ConversationHandler.END

def create_progress_bar(progress: float, length: int = 20) -> str:
    """Создает текстовый прогресс-бар"""
    filled = int(progress / 100 * length)
    empty = length - filled
    return '█' * filled + '░' * empty

def is_config_relevant(
    config: str, 
    target_country: str, 
    country_codes: list,
    additional_keywords: list = [],
    additional_patterns: list = []
) -> bool:
    """Проверка релевантности конфига"""
    if detect_by_keywords(config, target_country, additional_keywords, additional_patterns):
        return True
    
    domain = extract_domain(config)
    if domain:
        tld = domain.split('.')[-1].lower()
        if tld in country_codes:
            return True
    
    return False

def resolve_dns(host: str) -> str:
    """Разрешение DNS с кэшированием и повторными попытками"""
    if host in dns_cache:
        return dns_cache[host]
    
    try:
        if re.match(r'^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$', host):
            ip = host
        else:
            # Повторные попытки с экспоненциальной задержкой
            for attempt in range(MAX_RETRIES):
                try:
                    ip = socket.gethostbyname_ex(host)[-1][0]
                    break
                except (socket.gaierror, socket.timeout):
                    if attempt < MAX_RETRIES - 1:
                        delay = 2 ** attempt  # Экспоненциальная задержка
                        time.sleep(delay)
                    else:
                        raise
    
        dns_cache[host] = ip
        return ip
    except (socket.gaierror, socket.timeout):
        dns_cache[host] = None
        return None
    except Exception as e:
        logger.error(f"Ошибка разрешения DNS для {host}: {e}")
        dns_cache[host] = None
        return None

def geolocate_ip(ip: str) -> str:
    """Геолокация IP с использованием локальной базы данных"""
    if not geoip_reader:
        return None
    
    if ip in geo_cache:
        return geo_cache[ip]
    
    try:
        # Пропускаем приватные IP
        if re.match(r'(^127\.)|(^10\.)|(^172\.1[6-9]\.)|(^172\.2[0-9]\.)|(^172\.3[0-1]\.)|(^192\.168\.)', ip):
            geo_cache[ip] = None
            return None
        
        try:
            data = geoip_reader.get(ip)
            if not data:
                geo_cache[ip] = None
                return None
            
            # Извлекаем название страны
            country = data.get('country', {}).get('names', {}).get('en')
            if not country:
                country = data.get('registered_country', {}).get('names', {}).get('en')
            
            geo_cache[ip] = country
            return country
        except Exception as e:
            logger.error(f"Ошибка геолокации для {ip}: {e}")
            geo_cache[ip] = None
            return None
    
    except Exception as e:
        logger.error(f"Общая ошибка геолокации для {ip}: {e}")
        geo_cache[ip] = None
        return None

def detect_by_keywords(
    config: str, 
    target_country: str,
    additional_keywords: list = [],
    additional_patterns: list = []
) -> bool:
    """Обнаружение страны по ключевым словам"""
    patterns = {
        'japan': [r'jp\b', r'japan', r'tokyo', r'\.jp\b', r'日本', r'東京'],
        'united states': [r'us\b', r'usa\b', r'united states', r'new york', r'\.us\b', r'美国', r'紐約'],
        'russia': [r'ru\b', r'russia', r'moscow', r'\.ru\b', r'россия', r'俄国', r'москва'],
        'germany': [r'de\b', r'germany', r'frankfurt', r'\.de\b', r'германия', r'德国', r'フランクフルト'],
        'united kingdom': [r'uk\b', r'united kingdom', r'london', r'\.uk\b', r'英国', r'倫敦', r'gb'],
        'france': [r'france', r'paris', r'\.fr\b', r'法国', r'巴黎'],
        'brazil': [r'brazil', r'sao paulo', r'\.br\b', r'巴西', r'聖保羅'],
        'singapore': [r'singapore', r'\.sg\b', r'新加坡', r'星加坡'],
        'south korea': [r'korea', r'seoul', r'\.kr\b', r'韩国', r'首爾', r'korean'],
        'turkey': [r'turkey', r'istanbul', r'\.tr\b', r'土耳其', r'伊斯坦布爾'],
        'taiwan': [r'taiwan', r'taipei', r'\.tw\b', r'台湾', r'台北'],
        'switzerland': [r'switzerland', r'zurich', r'\.ch\b', r'瑞士', r'蘇黎世'],
        'india': [r'india', r'mumbai', r'\.in\b', r'印度', r'孟買'],
        'canada': [r'canada', r'toronto', r'\.ca\b', r'加拿大', r'多倫多'],
        'australia': [r'australia', r'sydney', r'\.au\b', r'澳洲', r'悉尼'],
        'china': [r'china', r'beijing', r'\.cn\b', r'中国', r'北京'],
        'italy': [r'italy', r'rome', r'\.it\b', r'意大利', r'羅馬'],
        'spain': [r'spain', r'madrid', r'\.es\b', r'西班牙', r'马德里'],
        'portugal': [r'portugal', r'lisbon', r'\.pt\b', r'葡萄牙', r'里斯本'],
        'norway': [r'norway', r'oslo', r'\.no\b', r'挪威', r'奥斯陆'],
        'finland': [r'finland', r'helsinki', r'\.fi\b', r'芬兰', r'赫尔辛基'],
        'denmark': [r'denmark', r'copenhagen', r'\.dk\b', r'丹麦', r'哥本哈根'],
        'poland': [r'poland', r'warsaw', r'\.pl\b', r'波兰', r'华沙'],
        'ukraine': [r'ukraine', r'kyiv', r'\.ua\b', r'乌克兰', r'基辅'],
        'belarus': [r'belarus', r'minsk', r'\.by\b', r'白俄罗斯', r'明斯克'],
        'indonesia': [r'indonesia', r'jakarta', r'\.id\b', r'印度尼西亚', r'雅加达'],
        'malaysia': [r'malaysia', r'kuala lumpur', r'\.my\b', r'马来西亚', r'吉隆坡'],
        'philippines': [r'philippines', r'manila', r'\.ph\b', r'菲律宾', r'马尼拉'],
        'vietnam': [r'vietnam', r'hanoi', r'\.vn\b', r'越南', r'河内'],
        'thailand': [r'thailand', r'bangkok', r'\.th\b', r'泰国', r'曼谷'],
        'czech republic': [r'czech', r'prague', r'\.cz\b', r'捷克', r'布拉格'],
        'romania': [r'romania', r'bucharest', r'\.ro\b', r'罗马尼亚', r'布加勒斯特'],
        'hungary': [r'hungary', r'budapest', r'\.hu\b', r'匈牙利', r'布达佩斯'],
        'greece': [r'greece', r'athens', r'\.gr\b', r'希腊', r'雅典'],
        'bulgaria': [r'bulgaria', r'sofia', r'\.bg\b', r'保加利亚', r'索非а'],
        'egypt': [r'egypt', r'cairo', r'\.eg\b', r'埃及', r'开罗'],
        'nigeria': [r'nigeria', r'abuja', r'\.ng\b', r'尼日利亚', r'阿布贾'],
        'kenya': [r'kenya', r'nairobi', r'\.ke\b', r'肯尼亚', r'内罗毕'],
        'colombia': [r'colombia', r'bogota', r'\.co\b', r'哥伦比亚', r'波哥大'],
        'peru': [r'peru', r'lima', r'\.pe\b', r'秘鲁', r'利马'],
        'chile': [r'chile', r'santiago', r'\.cl\b', r'智利', r'圣地亚哥'],
        'venezuela': [r'venezuela', r'caracas', r'\.ve\b', r'委内瑞拉', r'加拉加ス'],
        "austria": [r'austria', r'vienna', r'\.at\b', r'奥地利', r'维也纳'],
        "belgium": [r'belgium', r'brussels', r'\.be\b', r'比利时', r'布鲁塞尔'],
        "ireland": [r'ireland', r'dublin', r'\.ie\b', r'爱尔兰', r'都柏林'],
        "algeria": [r'algeria', r'algiers', r'\.dz\b', r'الجزائر', r'阿尔及利亚'],
        "angola": [r'angola', r'luanda', r'\.ao\b', r'安哥拉'],
        "bangladesh": [r'bangladesh', r'dhaka', r'\.bd\b', r'孟加拉'],
        "cambodia": [r'cambodia', r'phnom penh', r'\.kh\b', r'柬埔寨'],
        "costa rica": [r'costa rica', r'san jose', r'\.cr\b', r'哥斯达黎加'],
        "croatia": [r'croatia', r'zagreb', r'\.hr\b', r'克罗地亚'],
        "cuba": [r'cuba', r'havana', r'\.cu\b', r'古巴'],
        "estonia": [r'estonia', r'tallinn', r'\.ee\b', r'爱沙尼亚'],
        "georgia": [r'georgia', r'tbilisi', r'\.ge\b', r'格鲁吉亚'],
        "ghana": [r'ghana', r'accra', r'\.gh\b', r'加纳'],
        "iran": [r'iran', r'tehran', r'\.ir\b', r'伊朗'],
        "jordan": [r'jordan', r'ammam', r'\.jo\b', r'约旦'],
        "kazakhstan": [r'kazakhstan', r'astana', r'\.kz\b', r'哈萨克斯坦'],
        "kuwait": [r'kuwait', r'kuwait city', r'\.kw\b', r'科威特'],
        "lebanon": [r'lebanon', r'beirut', r'\.lb\b', r'黎巴嫩'],
        "libya": [r'libya', r'tripoli', r'\.ly\b', r'利比亚'],
        "morocco": [r'morocco', r'rabat', r'\.ma\b', r'摩洛哥'],
        "nepal": [r'nepal', r'kathmandu', r'\.np\b', r'尼泊尔'],
        "oman": [r'oman', r'muscat', r'\.om\b', r'阿曼'],
        "pakistan": [r'pakistan', r'islamabad', r'\.pk\b', r'巴基斯坦'],
        "qatar": [r'qatar', r'doha', r'\.qa\b', r'卡塔尔'],
        "serbia": [r'serbia', r'belgrade', r'\.rs\b', r'塞尔维亚'],
        "slovakia": [r'slovakia', r'bratislava', r'\.sk\b', r'斯洛伐克'],
        "slovenia": [r'slovenia', r'ljubljana', r'\.si\b', r'斯洛文尼亚'],
        "sudan": [r'sudan', r'khartoum', r'\.sd\b', r'苏丹'],
        "syria": [r'syria', r'damascus', r'\.sy\b', r'叙利亚'],
        "tunisia": [r'tunisia', r'tunis', r'\.tn\b', r'突尼斯'],
        "uruguay": [r'uruguay', r'montevideo', r'\.uy\b', r'乌拉圭'],
        "uzbekistan": [r'uzbekistan', r'tashkent', r'\.uz\b', r'乌兹别克斯坦'],
        "yemen": [r'yemen', r'sanaa', r'\.ye\b', r'也门']
    }
    
    # Добавляем улучшенные ключевые слова
    if target_country in patterns:
        patterns[target_country].extend(additional_keywords)
        patterns[target_country].extend(additional_patterns)
    
    # Быстрая проверка по ключевым словам
    if target_country in patterns:
        for pattern in patterns[target_country]:
            if re.search(pattern, config, re.IGNORECASE):
                return True
    return False

def extract_host(config: str) -> str:
    """Извлечение хоста из конфига с улучшенными паттернами"""
    try:
        # VMess
        if config.startswith('vmess://'):
            try:
                encoded = config.split('://')[1].split('?')[0]
                padding = '=' * (-len(encoded) % 4)
                decoded = base64.b64decode(encoded + padding).decode('utf-8', errors='replace')
                json_data = json.loads(decoded)
                return json_data.get('host') or json_data.get('add', '')
            except:
                # Альтернативное извлечение
                match = re.search(r'(?:"add"\\s*:\\s*")([^"]+)', config)
                if match:
                    return match.group(1)
                return None
        
        # VLESS/Trojan
        elif config.startswith(('vless://', 'trojan://')):
            parsed = urlparse(config)
            return parsed.hostname
        
        # Shadowsocks
        elif config.startswith('ss://'):
            try:
                parts = config.split('@')
                if len(parts) < 2:
                    return None
                host_port = parts[1].split('#')[0].split('/')[0]
                return host_port.split(':')[0]
            except:
                # Альтернативное извлечение
                match = re.search(r'@([a-z0-9.-]+):', config, re.IGNORECASE)
                if match:
                    return match.group(1)
                return None
        
        # ShadowsocksR
        elif config.startswith('ssr://'):
            try:
                encoded = config[6:].split('/')[0]
                padding = '=' * (-len(encoded) % 4)
                decoded = base64.b64decode(encoded + padding).decode()
                parts = decoded.split(':')
                if len(parts) > 2:
                    return parts[0]
            except:
                return None
        
        # SOCKS5/HTTP/HTTPS/Hysteria/Hysteria2/Brook
        elif any(config.startswith(proto) for proto in [
            'socks5://', 'http://', 'https://', 
            'hysteria://', 'hysteria2://', 'brook://'
        ]):
            parsed = urlparse(config)
            return parsed.hostname
        
        # WireGuard
        elif '[Interface]' in config and '[Peer]' in config:
            match = re.search(r'Endpoint\s*=\s*([\w.-]+):', config)
            return match.group(1) if match else None
        
        # OpenVPN
        elif 'openvpn' in config.lower():
            match = re.search(r'remote\s+([\w.-]+)\s+\d+', config)
            return match.group(1) if match else None
        
        # Общий случай
        else:
            # Расширенные паттерны для извлечения хоста
            patterns = [
                r'\b(?:\d{1,3}\.){3}\d{1,3}\b',  # IPv4
                r'([a-z0-9]+(-[a-z0-9]+)*\.)+[a-z]{2,}',  # Домен
                r'@([\w\.-]+):?',  # Формат user@host:port
                r'host\s*[:=]\s*"([^"]+)"',  # JSON-формат
                r'address\s*=\s*([\w\.-]+)'  # Конфигурационные файлы
            ]
            
            for pattern in patterns:
                match = re.search(pattern, config, re.IGNORECASE)
                if match:
                    return match.group(0)
    
    except Exception as e:
        logger.debug(f"Ошибка извлечения хоста: {e}")
    
    return None

def extract_domain(config: str) -> str:
    """Извлечение домена из конфига"""
    try:
        url_match = re.search(r'(?:https?://)?([a-z0-9.-]+\.[a-z]{2,})', config, re.IGNORECASE)
        if url_match:
            return url_match.group(1)
        
        domain_match = re.search(r'\b(?:[a-z0-9]+(-[a-z0-9]+)*\.)+[a-z]{2,}\b', config, re.IGNORECASE)
        if domain_match:
            return domain_match.group(0)
    
    except Exception as e:
        logger.debug(f"Ошибка извлечения домена: {e}")
    
    return None

async def cancel(update: Update, context: CallbackContext):
    """Отмена операции и очистка"""
    if 'file_path' in context.user_data:
        file_path = context.user_data['file_path']
        if os.path.exists(file_path):
            os.unlink(file_path)
        del context.user_data['file_path']
    if 'file_paths' in context.user_data:
        for file_path in context.user_data['file_paths']:
            if os.path.exists(file_path):
                os.unlink(file_path)
        del context.user_data['file_paths']
    
    clear_temporary_data(context)
    await update.message.reply_text("Операция отменена.")
    return ConversationHandler.END

def main() -> None:
    """Основная функция запуска бота"""
    # Инициализация базы геолокации
    loop = asyncio.get_event_loop()
    if not loop.run_until_complete(initialize_geoip_database()):
        logger.error("Не удалось загрузить базу геолокации. Строгий поиск будет недоступен")
    
    application = Application.builder().token(TOKEN).build()

    conv_handler = ConversationHandler(
        entry_points=[CommandHandler("check_configs", start_check)],
        states={
            START: [CallbackQueryHandler(start_choice)],
            WAITING_FILE: [
                MessageHandler(filters.Document.TEXT, handle_document),
                MessageHandler(filters.ALL & ~filters.COMMAND, 
                              lambda update, context: update.message.reply_text("❌ Пожалуйста, загрузите текстовый файл."))
            ],
            WAITING_COUNTRY: [
                CallbackQueryHandler(button_handler),
                MessageHandler(filters.TEXT & ~filters.COMMAND, handle_country)
            ],
            WAITING_MODE: [CallbackQueryHandler(button_handler)],
            WAITING_NUMBER: [MessageHandler(filters.TEXT & ~filters.COMMAND, handle_number)],
            SENDING_CONFIGS: [CallbackQueryHandler(button_handler)],
            PROCESSING_STRICT: [CallbackQueryHandler(button_handler)]
        },
        fallbacks=[CommandHandler("cancel", cancel)],
        allow_reentry=True,
        per_user=True
    )
    
    application.add_handler(conv_handler)

    port = int(os.environ.get('PORT', 5000))
    external_host = os.environ.get('RENDER_EXTERNAL_HOSTNAME')
    
    if external_host:
        webhook_url = f"https://{external_host}/webhook"
        logger.info(f"Запуск в режиме webhook: {webhook_url}")
        application.run_webhook(
            listen="0.0.0.0",
            port=port,
            url_path="/webhook",
            webhook_url=webhook_url,
            drop_pending_updates=True
        )
    else:
        logger.info("Запуск в режиме polling")
        application.run_polling()

if __name__ == "__main__":
    main()
