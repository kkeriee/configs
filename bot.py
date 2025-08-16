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

# Конфигурация
TOKEN = os.getenv("TELEGRAM_BOT_TOKEN")
NEURAL_API_KEY = os.getenv("NEURAL_API_KEY")
MAX_FILE_SIZE = 15 * 1024 * 1024  # 15 МБ
MAX_MSG_LENGTH = 4000
GEOIP_API = "http://ip-api.com/json/"
HEADERS = {'User-Agent': 'Telegram V2Ray Config Bot/3.0'}
MAX_WORKERS = 10
CHUNK_SIZE = 500  # Увеличен размер чанка
NEURAL_MODEL = "deepseek/deepseek-r1-0528"
NEURAL_TIMEOUT = 15  # Таймаут для нейросети

# Состояния диалога
START, WAITING_FILE, WAITING_COUNTRY, WAITING_MODE, WAITING_NUMBER, SENDING_CONFIGS, PROCESSING_STRICT = range(7)

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
    
    # Проверка кэша нормализации
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
        "ирландия": "ireland", "ie": "ireland", "ирл": "ireland"
    }
    for key, value in ru_en_map.items():
        text = text.replace(key, value)
    return text

async def neural_normalize_country(text: str) -> str:
    """Нормализация страны с помощью нейросети"""
    if not neural_client:
        return None
    
    # Проверка кэша
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
                country_cache[text] = country_name  # Кэшируем результат
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
    
    # Проверка кэша
    config_hash = hash(config)
    if config_hash in config_cache:
        return config_cache[config_hash]
    
    system_prompt = (
        "Определи страну для этого V2Ray конфига. Ответь только названием страны на английском в нижнем регистре "
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
        
        config_cache[config_hash] = result  # Кэшируем результат
        return result
    except Exception as e:
        logger.error(f"Ошибка нейросети при определении страны конфига: {e}")
        return None

async def generate_country_instructions(country: str) -> str:
    """Генерация инструкций для страны с помощью нейросети"""
    if not neural_client:
        return "Инструкции недоступны ( нейросеть отключена)"
    
    # Проверка кэша
    if country in instruction_cache:
        return instruction_cache[country]
    
    system_prompt = (
        f"Ты эксперт по VPN. Сгенерируй краткую инструкцию по использованию V2Ray для пользователей из {country}. "
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
        instruction_cache[country] = instructions  # Кэшируем результат
        return instructions
    except Exception as e:
        logger.error(f"Ошибка генерации инструкций: {e}")
        return f"⚠️ Не удалось сгенерировать инструкцию для {country}"

async def neural_improve_search(country: str) -> dict:
    """Улучшение поиска с помощью нейросети"""
    if not neural_client:
        return None
    
    # Проверка кэша
    if country in neural_improvement_cache:
        return neural_improvement_cache[country]
    
    system_prompt = (
        "Ты — поисковый агент для бота V2Ray. Сгенерируй улучшенные инструкции для поиска конфигов в указанной стране. "
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
        neural_improvement_cache[country] = improvement  # Кэшируем результат
        return improvement
    except Exception as e:
        logger.error(f"Ошибка улучшения поиска: {e}")
        return None

async def start_check(update: Update, context: CallbackContext):
    """Начало проверки конфигов с выбором действия"""
    clear_temporary_data(context)
    user_id = update.message.from_user.id
    
    # Проверяем наличие истории
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
        await update.message.reply_text("📎 Пожалуйста, загрузите текстовый файл с конфигурациями V2Ray (до 15 МБ).")
        return WAITING_FILE

async def handle_document(update: Update, context: CallbackContext):
    """Обработка загруженного файла"""
    user = update.message.from_user
    document = update.message.document
    
    # Проверка типа файла
    if not document.mime_type.startswith('text/'):
        await update.message.reply_text("❌ Пожалуйста, загрузите текстовый файл.")
        return ConversationHandler.END
    
    # Проверка размера файла
    if document.file_size > MAX_FILE_SIZE:
        await update.message.reply_text(
            f"❌ Файл слишком большой. Максимальный размер: {MAX_FILE_SIZE//1024//1024}MB"
        )
        return ConversationHandler.END
    
    # Скачивание файла
    file = await context.bot.get_file(document.file_id)
    with tempfile.NamedTemporaryFile(delete=False) as tmp_file:
        await file.download_to_memory(tmp_file)
        tmp_file.seek(0)
        content = tmp_file.read().decode('utf-8', errors='replace')
        lines = content.splitlines()
        configs = [line.strip() for line in lines if line.strip()]
        context.user_data['configs'] = configs
        context.user_data['file_name'] = document.file_name
        tmp_file_path = tmp_file.name
    
    # Удаление временного файла
    if os.path.exists(tmp_file_path):
        os.unlink(tmp_file_path)
    
    logger.info(f"Пользователь {user.id} загрузил файл: {document.file_name} ({len(configs)} конфигов)")
    
    # Клавиатура действий
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
        await fast_search(update, context)  # Прямой вызов
        return WAITING_NUMBER
    
    elif query.data == 'strict_mode':
        context.user_data['search_mode'] = 'strict'
        await query.edit_message_text("🔍 Запускаю строгий поиск...")
        await strict_search(update, context)  # Прямой вызов
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
    """Обработка выбора действия в начале"""
    return await button_handler(update, context)

async def handle_country(update: Update, context: CallbackContext):
    """Обработка ввода страны"""
    country_request = update.message.text
    context.user_data['country_request'] = country_request
    normalized_text = normalize_text(country_request)
    
    logger.info(f"Нормализованный текст: {normalized_text}")
    country = None
    found_by_neural = False
    
    # Поиск страны через pycountry
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
                
                # Сохраняем в кэш нормализации
                country_normalization_cache[country_request] = neural_country
                if normalized_text != country_request:
                    country_normalization_cache[normalized_text] = neural_country
            except:
                logger.warning("Нейросеть не смогла определить страну")
    
    # Если страна не найдена
    if not country:
        logger.warning(f"Страна не распознана: {country_request}")
        
        # Попытка улучшить поиск через нейросеть
        if neural_client:
            try:
                improved_search = await neural_improve_search(country_request)
                if improved_search:
                    keywords = improved_search.get('keywords', [])
                    patterns = improved_search.get('patterns', [])
                    logger.info(f"Улучшенный поиск: keywords={keywords}, patterns={patterns}")
                    
                    # Сохраняем улучшения для будущих запросов
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

    # Сохраняем данные о стране
    context.user_data['country'] = country.name
    context.user_data['target_country'] = country.name.lower()
    context.user_data['country_codes'] = [c.alpha_2.lower() for c in countries] + [country.alpha_2.lower()]
    
    # Клавиатура выбора режима
    keyboard = [
        [
            InlineKeyboardButton("⚡ Быстрый поиск", callback_data='fast_mode'),
            InlineKeyboardButton("🔍 Строгий поиск", callback_data='strict_mode')
        ]
    ]
    reply_markup = InlineKeyboardMarkup(keyboard)
    
    # Генерация инструкций, если их нет в кэше
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
    
    # Применяем улучшения поиска если есть
    improved_search = context.user_data.get('improved_search', {})
    additional_keywords = improved_search.get('keywords', [])
    additional_patterns = improved_search.get('patterns', [])
    
    # Поиск релевантных конфигов
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
        
        # Обновление прогресса каждые 500 конфигов
        if i % 500 == 0 or i == total_configs - 1:
            progress = min((i + 1) / total_configs * 100, 100)
            progress_bar = create_progress_bar(progress)
            await context.bot.edit_message_text(
                chat_id=user_id,
                message_id=progress_msg.message_id,
                text=f"🔎 Быстрый поиск: {progress_bar} {progress:.1f}%\nОбработано: {i+1}/{total_configs}"
            )
    
    # Результаты поиска
    logger.info(f"Найдено {len(matched_configs)} конфигов для {context.user_data['country']}, обработка заняла {time.time()-start_time:.2f} сек")
    
    if not matched_configs:
        await context.bot.edit_message_text(
            chat_id=user_id,
            message_id=progress_msg.message_id,
            text=f"❌ Конфигурации для {context.user_data['country']} не найдены."
        )
        return ConversationHandler.END
    
    # Сохраняем результаты
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

async def strict_search(update: Update, context: CallbackContext):
    """Строгий поиск конфигов с проверкой геолокации"""
    user_id = update.callback_query.from_user.id if update.callback_query else update.message.from_user.id
    configs = context.user_data.get('configs', [])
    target_country = context.user_data.get('target_country', '')
    
    if not configs or not target_country:
        await context.bot.send_message(chat_id=user_id, text="❌ Ошибка: данные для поиска отсутствуют.")
        return ConversationHandler.END
    
    # Этап 1: предварительная фильтрация
    start_time = time.time()
    prelim_configs = []
    progress_msg = await context.bot.send_message(chat_id=user_id, text="🔎 Этап 1: предварительная фильтрация...")
    
    # Применяем улучшения поиска если есть
    improved_search = context.user_data.get('improved_search', {})
    additional_keywords = improved_search.get('keywords', [])
    additional_patterns = improved_search.get('patterns', [])
    
    # Поиск релевантных конфигов
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
        
        # Обновление прогресса каждые 500 конфигов
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
    
    # Этап 2: строгая проверка через геолокацию IP
    total_chunks = (len(prelim_configs) + CHUNK_SIZE - 1) // CHUNK_SIZE
    # Создаем клавиатуру с кнопкой остановки
    stop_keyboard = [[InlineKeyboardButton("⏹ Остановить строгий поиск", callback_data='stop_strict_search')]]
    stop_reply_markup = InlineKeyboardMarkup(stop_keyboard)
    
    await context.bot.edit_message_text(
        chat_id=user_id,
        message_id=progress_msg.message_id,
        text=f"🌐 Начинаю проверку геолокации {len(prelim_configs)} конфигов...\n"
        f"Всего секторов: {total_chunks}",
        reply_markup=stop_reply_markup
    )
    
    start_time = time.time()
    strict_matched_configs = []
    context.user_data['strict_in_progress'] = True  # Флаг, что строгий поиск в процессе
    
    # Обрабатываем чанки конфигов
    for chunk_idx in range(total_chunks):
        if context.user_data.get('stop_strict_search'):
            break
            
        start_idx = chunk_idx * CHUNK_SIZE
        end_idx = min((chunk_idx+1) * CHUNK_SIZE, len(prelim_configs))
        chunk = prelim_configs[start_idx:end_idx]
        chunk_start_time = time.time()
        
        # Проверяем конфиги в чанке
        valid_configs = validate_configs_by_geolocation(chunk, target_country)
        strict_matched_configs.extend(valid_configs)
        
        # Обновляем сообщение прогресса
        chunk_time = time.time() - chunk_start_time
        chunk_progress = min((chunk_idx + 1) / total_chunks * 100, 100)
        progress_bar = create_progress_bar(chunk_progress)
        await context.bot.edit_message_text(
            chat_id=user_id,
            message_id=progress_msg.message_id,
            text=f"🌐 Этап 2: {progress_bar} {chunk_progress:.1f}%\n"
                 f"Обработан сектор: {chunk_idx+1}/{total_chunks}\n"
                 f"Найдено: {len(valid_configs)} | Всего: {len(strict_matched_configs)}\n"
                 f"Скорость: {len(chunk)/chunk_time:.1f} конфиг/сек",
            reply_markup=stop_reply_markup
        )
    
    # Убираем флаг
    context.user_data['strict_in_progress'] = False
    
    total_time = time.time() - start_time
    logger.info(f"Строгая проверка завершена: найдено {len(strict_matched_configs)} конфигов, заняло {total_time:.2f} сек")
    
    if context.user_data.get('stop_strict_search'):
        # Удаляем кнопку остановки, редактируя сообщение
        await context.bot.edit_message_text(
            chat_id=user_id,
            message_id=progress_msg.message_id,
            text=f"⏹ Строгий поиск остановлен. Найдено {len(strict_matched_configs)} конфигов."
        )
    else:
        await context.bot.edit_message_text(
            chat_id=user_id,
            message_id=progress_msg.message_id,
            text=f"✅ Строгий поиск завершен. Найдено {len(strict_matched_configs)} конфигов."
        )
    
    if not strict_matched_configs:
        await context.bot.send_message(chat_id=user_id, text="❌ Конфигурации не найдены.")
        return ConversationHandler.END
    
    # Сохраняем все найденные конфиги
    context.user_data['matched_configs'] = strict_matched_configs
    
    await context.bot.send_message(
        chat_id=user_id,
        text=f"🌍 Для страны {context.user_data['country']} найдено {len(strict_matched_configs)} валидных конфигов! Сколько конфигов прислать? (введите число от 1 до {len(strict_matched_configs)})"
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
        
        # Перемешиваем конфиги для случайной выборки
        random.shuffle(matched_configs)
        selected_configs = matched_configs[:num]
        
        # Сохраняем выбранные конфиги
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
    
    # Формируем заголовок
    header = f"Конфиги для {country_name}:\n\n"
    configs_text = ""
    messages = []
    
    # Собираем конфиги в сообщения с учетом лимита
    for config in matched_configs:
        config_line = f"{config}\n"
        
        # Если добавление конфига превысит лимит
        if len(header) + len(configs_text) + len(config_line) > MAX_MSG_LENGTH:
            # Сохраняем текущее сообщение
            messages.append(header + configs_text)
            # Начинаем новое сообщение
            configs_text = ""
        
        configs_text += config_line
    
    # Добавляем последнее сообщение
    if configs_text:
        messages.append(header + configs_text)
    
    # Отправляем все сообщения
    total_messages = len(messages)
    for i, message in enumerate(messages):
        if context.user_data.get('stop_sending'):
            await context.bot.send_message(chat_id=user_id, text="⏹ Отправка остановлена.")
            return ConversationHandler.END
        
        try:
            # Добавляем прогресс в последнее сообщение
            if i == total_messages - 1:
                progress = f"\n\n⌛ Прогресс: {i+1}/{total_messages} сообщений"
                if len(message) + len(progress) <= MAX_MSG_LENGTH:
                    message += progress
            
            await context.bot.send_message(
                chat_id=user_id,
                text=f"<pre>{message}</pre>",
                parse_mode='HTML'
            )
            await asyncio.sleep(0.3)  # Задержка для избежания флуда
        except Exception as e:
            logger.error(f"Ошибка отправки сообщения: {e}")
    
    await context.bot.send_message(chat_id=user_id, text="✅ Все конфиги отправлены.")
    
    # Сохраняем историю
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
    # Проверка по ключевым словам
    if detect_by_keywords(config, target_country, additional_keywords, additional_patterns):
        return True
    
    # Проверка по домену
    domain = extract_domain(config)
    if domain:
        tld = domain.split('.')[-1].lower()
        if tld in country_codes:
            return True
    
    return False

def validate_configs_by_geolocation(configs: list, target_country: str) -> list:
    """Проверка конфигов по геолокации IP"""
    valid_configs = []
    
    # Используем ThreadPoolExecutor для параллельной обработки
    with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        # Создаем задачи для каждого конфига
        futures = {executor.submit(validate_config_by_geolocation, config, target_country): config for config in configs}
        
        # Обрабатываем результаты по мере их готовности
        for future in concurrent.futures.as_completed(futures):
            config = futures[future]
            try:
                if future.result():
                    valid_configs.append(config)
            except Exception as e:
                logger.error(f"Ошибка проверки конфига: {e}")
    
    return valid_configs

def validate_config_by_geolocation(config: str, target_country: str) -> bool:
    """Проверка конфига по геолокации IP"""
    try:
        # Пропускаем невалидные конфиги
        if not validate_config_structure(config):
            return False
        
        # Извлекаем хост из конфига
        host = extract_host(config)
        if not host:
            return False
        
        # Разрешаем DNS (если это домен)
        ip = resolve_dns(host)
        if not ip:
            return False
        
        # Получаем страну по IP
        country = geolocate_ip(ip)
        if not country:
            return False
        
        # Сравниваем страну с целевой
        return country.lower() == target_country.lower()
    
    except Exception as e:
        logger.error(f"Ошибка проверки конфига: {e}")
        return False

def validate_config_structure(config: str) -> bool:
    """Проверка структуры конфига"""
    if config.startswith('vmess://'):
        try:
            encoded = config.split('://')[1].split('?')[0]
            padding = '=' * (-len(encoded) % 4)
            decoded = base64.b64decode(encoded + padding).decode('utf-8', errors='replace')
            json_data = json.loads(decoded)
            required_fields = ['v', 'add', 'port', 'id']
            return all(field in json_data for field in required_fields)
        except:
            return False
    elif config.startswith('vless://'):
        try:
            parsed = urlparse(config)
            if not parsed.hostname:
                return False
            uuid = parsed.username
            if not uuid or len(uuid) != 36:
                return False
            return True
        except:
            return False
    return bool(re.search(r'\b(?:\d{1,3}\.){3}\d{1,3}:\d+\b', config))

def resolve_dns(host: str) -> str:
    """Разрешение DNS с кэшированием"""
    # Проверка кэша
    if host in dns_cache:
        return dns_cache[host]
    
    try:
        if re.match(r'\d+\.\d+\.\d+\.\d+', host):
            ip = host
        else:
            ip = socket.gethostbyname(host)
        
        # Кэширование результата
        dns_cache[host] = ip
        return ip
    except:
        dns_cache[host] = None  # Кэшируем отрицательный результат
        return None

def geolocate_ip(ip: str) -> str:
    """Геолокация IP с кэшированием"""
    # Проверка кэша
    if ip in geo_cache:
        return geo_cache[ip]
    
    try:
        # Пропускаем приватные IP
        if re.match(r'(10\.|192\.168\.|172\.(1[6-9]|2[0-9]|3[0-1])\.)', ip):
            geo_cache[ip] = None
            return None
        
        # Запрос к API
        response = requests.get(f"{GEOIP_API}{ip}", headers=HEADERS, timeout=3)
        data = response.json()
        
        if data.get('status') == 'success':
            country = data.get('country')
            # Кэширование результата
            geo_cache[ip] = country
            return country
    except Exception as e:
        logger.error(f"Ошибка геолокации для {ip}: {e}")
    
    geo_cache[ip] = None  # Кэшируем отрицательный результат
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
        "ireland": [r'ireland', r'dublin', r'\.ie\b', r'爱尔兰', r'都柏林']
    }
    
    # Добавляем дополнительные ключевые слова и шаблоны
    if target_country in patterns:
        patterns[target_country].extend(additional_keywords)
        patterns[target_country].extend(additional_patterns)
    
    if target_country in patterns:
        for pattern in patterns[target_country]:
            if re.search(pattern, config, re.IGNORECASE):
                return True
    return False

def extract_host(config: str) -> str:
    """Извлечение хоста из конфига"""
    if config.startswith('vmess://'):
        try:
            encoded = config.split('://')[1].split('?')[0]
            padding = '=' * (-len(encoded) % 4)
            decoded = base64.b64decode(encoded + padding).decode('utf-8', errors='replace')
            json_data = json.loads(decoded)
            host = json_data.get('host') or json_data.get('add', '')
            if host:
                return host
        except Exception as e:
            logger.debug(f"Ошибка декодирования VMESS: {e}")
    elif config.startswith('vless://'):
        try:
            parsed = urlparse(config)
            host = parsed.hostname
            if host:
                return host
        except Exception as e:
            logger.debug(f"Ошибка парсинга VLESS: {e}")
    
    host_match = re.search(r'\b(?:\d{1,3}\.){3}\d{1,3}\b', config)
    if host_match:
        return host_match.group(0)
    
    domain = extract_domain(config)
    if domain:
        return domain
    
    return None

def extract_domain(config: str) -> str:
    """Извлечение домена из конфига"""
    url_match = re.search(r'(?:https?://)?([a-z0-9.-]+\.[a-z]{2,})', config, re.IGNORECASE)
    if url_match:
        return url_match.group(1)
    
    domain_match = re.search(r'\b(?:[a-z0-9]+(-[a-z0-9]+)*\.)+[a-z]{2,}\b', config, re.IGNORECASE)
    if domain_match:
        return domain_match.group(0)
    
    return None

async def cancel(update: Update, context: CallbackContext):
    """Отмена операции и очистка"""
    # Удаляем временные файлы, если есть
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
    
    # Очищаем временные данные
    clear_temporary_data(context)
    await update.message.reply_text("Операция отменена.")
    return ConversationHandler.END

def main() -> None:
    """Основная функция запуска бота"""
    application = Application.builder().token(TOKEN).build()

    # Обработчик диалога
    conv_handler = ConversationHandler(
        entry_points=[CommandHandler("check_configs", start_check)],
        states={
            START: [
                CallbackQueryHandler(start_choice)
            ],
            WAITING_FILE: [
                MessageHandler(filters.Document.TEXT, handle_document),
                MessageHandler(filters.ALL & ~filters.COMMAND, 
                              lambda update, context: update.message.reply_text("❌ Пожалуйста, загрузите текстовый файл."))
            ],
            WAITING_COUNTRY: [
                CallbackQueryHandler(button_handler),
                MessageHandler(filters.TEXT & ~filters.COMMAND, handle_country)
            ],
            WAITING_MODE: [
                CallbackQueryHandler(button_handler)
            ],
            WAITING_NUMBER: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, handle_number)
            ],
            SENDING_CONFIGS: [
                CallbackQueryHandler(button_handler)
            ],
            PROCESSING_STRICT: [
                CallbackQueryHandler(button_handler)
            ]
        },
        fallbacks=[CommandHandler("cancel", cancel)],
        allow_reentry=True,
        per_user=True
    )
    
    application.add_handler(conv_handler)

    # Определение режима запуска
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
