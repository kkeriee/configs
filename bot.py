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
MAX_FILE_SIZE = 15 * 1024 * 1024
MAX_MSG_LENGTH = 4000
GEOIP_API = "http://ip-api.com/json/"
HEADERS = {'User-Agent': 'Telegram V2Ray Config Bot/1.0'}
MAX_WORKERS = 5
CHUNK_SIZE = 100
MAX_CONFIGS_PER_USER = 5000
NEURAL_MODEL = "deepseek/deepseek-r1-0528"

# Состояния диалога
WAITING_FILE, WAITING_COUNTRY, WAITING_MODE, SENDING_CONFIGS = range(4)

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
    )
    logger.info("Нейросеть DeepSeek-R1 инициализирована")
else:
    logger.warning("NEURAL_API_KEY не установлен, функции нейросети отключены")

def normalize_text(text: str) -> str:
    text = text.lower().strip()
    ru_en_map = {
        "россия": "russia", "русский": "russia", "рф": "russia", "ру": "russia",
        "сша": "united states", "америка": "united states", "usa": "united states", 
        "us": "united states", "соединенные штаты": "united states",
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
    sorted_keys = sorted(ru_en_map.keys(), key=len, reverse=True)
    for key in sorted_keys:
        text = text.replace(key, ru_en_map[key])
    return text

async def neural_normalize_country(text: str) -> str:
    if not neural_client:
        return None
    system_prompt = (
        "Ты эксперт по географии. Пользователь вводит название страны. "
        "Определи, какая страна имеется в виду, и верни её каноническое английское название в нижнем регистре. "
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
                return country.name.lower()
            except:
                return result
        return None
    except Exception as e:
        logger.error(f"Ошибка нейросети: {e}")
        return None

async def neural_detect_country(config: str) -> str:
    if not neural_client:
        return None
    system_prompt = (
        "Ты эксперт по V2Ray конфигурациям. Определи, для какой страны предназначен этот конфиг. "
        "Ответь только названием страны на английском в нижнем регистре или 'unknown', если не удалось определить."
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
        return result
    except Exception as e:
        logger.error(f"Ошибка нейросети при определении страны конфига: {e}")
        return None

async def check_configs(update: Update, context: CallbackContext):
    context.user_data.clear()
    await update.message.reply_text(
        "Пожалуйста, загрузите текстовый файл с конфигурациями V2RayTun."
    )
    return WAITING_FILE

async def handle_document(update: Update, context: CallbackContext):
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
        context.user_data['file_path'] = tmp_file.name
        context.user_data['file_name'] = document.file_name
    logger.info(f"Пользователь {user.id} загрузил файл: {document.file_name} ({document.file_size} байт)")
    keyboard = [
        [InlineKeyboardButton("📤 Загрузить еще файл", callback_data='add_file')],
        [InlineKeyboardButton("🌍 Указать страну", callback_data='set_country')]
    ]
    reply_markup = InlineKeyboardMarkup(keyboard)
    await update.message.reply_text(
        f"✅ Файл '{document.file_name}' успешно загружен. Вы можете:",
        reply_markup=reply_markup
    )
    return WAITING_COUNTRY

async def button_handler(update: Update, context: CallbackContext) -> int:
    query = update.callback_query
    await query.answer()
    if query.data == 'add_file':
        await query.edit_message_text("Пожалуйста, загрузите дополнительный файл с конфигурациями.")
        return WAITING_FILE
    elif query.data == 'set_country':
        await query.edit_message_text("Введите название страны (на русском или английском):")
        return WAITING_COUNTRY
    elif query.data == 'fast_mode':
        context.user_data['search_mode'] = 'fast'
        await process_search(update, context)
        return SENDING_CONFIGS
    elif query.data == 'strict_mode':
        context.user_data['search_mode'] = 'strict'
        await process_search(update, context)
        return SENDING_CONFIGS
    elif query.data == 'stop_sending':
        context.user_data['stop_sending'] = True
        await query.edit_message_text("⏹ Отправка конфигов остановлена.")
        return ConversationHandler.END
    return context.user_data.get('current_state', WAITING_COUNTRY)

async def handle_country(update: Update, context: CallbackContext):
    country_request = update.message.text
    context.user_data['country_request'] = country_request
    normalized_text = normalize_text(country_request)
    logger.info(f"Нормализованный текст: {normalized_text}")
    country = None
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
                logger.info(f"Нейросеть определила страну: {country.name}")
            except:
                logger.warning("Нейросеть не смогла определить страну")
    if not country:
        logger.warning(f"Страна не распознана: {country_request}")
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
    await update.message.reply_text(
        f"Вы выбрали страну: {country.name}\nВыберите режим поиска:",
        reply_markup=reply_markup
    )
    return WAITING_MODE

async def process_search(update: Update, context: CallbackContext):
    query = update.callback_query
    if query:
        await query.answer()
        user_id = query.from_user.id
    else:
        user_id = update.message.from_user.id
    country_request = context.user_data.get('country_request', '')
    search_mode = context.user_data.get('search_mode', 'fast')
    if not country_request:
        await context.bot.send_message(chat_id=user_id, text="❌ Ошибка: страна не указана.")
        return ConversationHandler.END
    logger.info(f"Пользователь {user_id} запросил страну: {country_request} в режиме {search_mode}")
    
    file_paths = context.user_data.get('file_paths', [])
    if not file_paths:
        if 'file_path' in context.user_data:
            file_paths = [context.user_data['file_path']]
            context.user_data['file_paths'] = file_paths
    if not file_paths:
        logger.error("Пути к файлам не найдены")
        await context.bot.send_message(chat_id=user_id, text="❌ Ошибка: файлы конфигурации не найдены.")
        return ConversationHandler.END
    
    all_configs = []
    for file_path in file_paths:
        try:
            await context.bot.send_message(chat_id=user_id, text="⏳ Идет чтение файла...")
            start_time = time.time()
            with open(file_path, 'r', encoding='utf-8', errors='replace') as f:
                configs = f.read().splitlines()
            logger.info(f"Файл прочитан: {len(configs)} строк, за {time.time()-start_time:.2f} сек")
            all_configs.extend(configs)
        except Exception as e:
            logger.error(f"Ошибка чтения файла: {e}")
            await context.bot.send_message(chat_id=user_id, text=f"❌ Ошибка обработки файла: {e}")
    if not all_configs:
        await context.bot.send_message(chat_id=user_id, text="❌ В файлах не найдено конфигураций.")
        return ConversationHandler.END
    
    if len(all_configs) > MAX_CONFIGS_PER_USER:
        all_configs = all_configs[:MAX_CONFIGS_PER_USER]
        await context.bot.send_message(
            chat_id=user_id, 
            text=f"⚠️ Внимание: обрабатывается только первые {MAX_CONFIGS_PER_USER} конфигов из-за ограничений."
        )
    context.user_data['all_configs'] = all_configs
    
    if search_mode == 'fast':
        await context.bot.send_message(chat_id=user_id, text="🔎 Начинаю быстрый поиск конфигов...")
        await fast_search(update, context)
    else:
        await context.bot.send_message(chat_id=user_id, text="🔍 Начинаю строгий поиск конфигов...")
        await strict_search(update, context)
    return SENDING_CONFIGS

async def fast_search(update: Update, context: CallbackContext):
    user_id = update.callback_query.from_user.id if update.callback_query else update.message.from_user.id
    all_configs = context.user_data.get('all_configs', [])
    target_country = context.user_data.get('target_country', '')
    if not all_configs or not target_country:
        await context.bot.send_message(chat_id=user_id, text="❌ Ошибка: данные для поиска отсутствуют.")
        return ConversationHandler.END
    
    start_time = time.time()
    matched_configs = []
    flag_pattern = get_country_flag_pattern(context.user_data['country'])
    for i, config in enumerate(all_configs):
        if not config.strip():
            continue
        try:
            if is_config_relevant(config, target_country, context.user_data['country_codes'], flag_pattern):
                matched_configs.append(config)
        except Exception as e:
            logger.error(f"Ошибка проверки конфига #{i}: {e}")
            continue
        if i % 1000 == 0 and i > 0:
            logger.info(f"Обработано {i}/{len(all_configs)} конфигов...")
    logger.info(f"Найдено {len(matched_configs)} конфигов для {context.user_data['country']}, обработка заняла {time.time()-start_time:.2f} сек")
    if not matched_configs:
        await context.bot.send_message(chat_id=user_id, text=f"❌ Конфигурации для {context.user_data['country']} не найдены.")
        return ConversationHandler.END
    context.user_data['matched_configs'] = matched_configs
    context.user_data['current_index'] = 0
    context.user_data['stop_sending'] = False
    await send_configs(update, context)

async def strict_search(update: Update, context: CallbackContext):
    user_id = update.callback_query.from_user.id if update.callback_query else update.message.from_user.id
    all_configs = context.user_data.get('all_configs', [])
    target_country = context.user_data.get('target_country', '')
    if not all_configs or not target_country:
        await context.bot.send_message(chat_id=user_id, text="❌ Ошибка: данные для поиска отсутствуют.")
        return ConversationHandler.END
    
    await context.bot.send_message(chat_id=user_id, text="🔎 Этап 1: предварительная фильтрация конфигов...")
    start_time = time.time()
    prelim_configs = []
    flag_pattern = get_country_flag_pattern(context.user_data['country'])
    for i, config in enumerate(all_configs):
        if not config.strip():
            continue
        try:
            if is_config_relevant(config, target_country, context.user_data['country_codes'], flag_pattern):
                prelim_configs.append(config)
        except Exception as e:
            logger.error(f"Ошибка быстрой проверки конфига #{i}: {e}")
            continue
        if i % 1000 == 0 and i > 0:
            logger.info(f"Обработано {i}/{len(all_configs)} конфигов...")
    logger.info(f"Предварительно найдено {len(prelim_configs)} конфигов для {context.user_data['country']}, обработка заняла {time.time()-start_time:.2f} сек")
    if not prelim_configs:
        await context.bot.send_message(chat_id=user_id, text=f"❌ Конфигурации для {context.user_data['country']} не найдены.")
        return ConversationHandler.END
    
    total_chunks = (len(prelim_configs) + CHUNK_SIZE - 1) // CHUNK_SIZE
    await context.bot.send_message(
        chat_id=user_id,
        text=f"🔍 Начинаю строгую проверку {len(prelim_configs)} конфигов секторами по {CHUNK_SIZE}...\n"
        f"Всего секторов: {total_chunks}"
    )
    start_time = time.time()
    strict_matched_configs = []
    for chunk_idx in range(0, len(prelim_configs), CHUNK_SIZE):
        if context.user_data.get('stop_sending'):
            break
        chunk = prelim_configs[chunk_idx:chunk_idx + CHUNK_SIZE]
        chunk_start_time = time.time()
        valid_configs = strict_config_check(chunk, target_country)
        strict_matched_configs.extend(valid_configs)
        chunk_end_time = time.time()
        chunk_time = chunk_end_time - chunk_start_time
        if chunk_idx + CHUNK_SIZE < len(prelim_configs):
            await context.bot.send_message(
                chat_id=user_id,
                text=f"✅ Сектор {chunk_idx//CHUNK_SIZE + 1}/{total_chunks} обработан\n"
                f"Найдено конфигов: {len(valid_configs)}\n"
                f"Время обработки: {chunk_time:.1f} сек\n"
                f"Всего найдено: {len(strict_matched_configs)}"
            )
        if valid_configs:
            context.user_data['matched_configs'] = valid_configs
            context.user_data['current_index'] = 0
            await send_configs(update, context)
    total_time = time.time() - start_time
    logger.info(f"Строгая проверка завершена: найдено {len(strict_matched_configs)} конфигов, заняло {total_time:.2f} сек")
    if not strict_matched_configs:
        await context.bot.send_message(chat_id=user_id, text=f"❌ Конфигурации для {context.user_data['country']} не найдены.")
        return ConversationHandler.END
    context.user_data['matched_configs'] = strict_matched_configs
    context.user_data['current_index'] = 0
    context.user_data['stop_sending'] = False
    await send_configs(update, context)

async def send_configs(update: Update, context: CallbackContext):
    user_id = update.callback_query.from_user.id if update.callback_query else update.message.from_user.id
    matched_configs = context.user_data.get('matched_configs', [])
    current_index = context.user_data.get('current_index', 0)
    country_name = context.user_data.get('country', '')
    stop_sending = context.user_data.get('stop_sending', False)
    if not matched_configs or current_index >= len(matched_configs) or stop_sending:
        if not stop_sending and current_index < len(matched_configs):
            await context.bot.send_message(chat_id=user_id, text="✅ Все конфиги отправлены.")
        return ConversationHandler.END
    
    stop_button = [[InlineKeyboardButton("⏹ Остановить отправку", callback_data='stop_sending')]]
    reply_markup = InlineKeyboardMarkup(stop_button)
    
    header = f"Конфиги для {country_name}:\n"
    message = header
    sent_count = 0
    flag = get_country_flag(context.user_data['country'])
    while current_index < len(matched_configs):
        config = matched_configs[current_index]
        config_line = f"{flag} {config}\n" if flag else f"{config}\n"
        if len(message) + len(config_line) > MAX_MSG_LENGTH:
            break
        message += config_line
        current_index += 1
        sent_count += 1
        if sent_count >= 20:
            break
    
    try:
        if message.strip() != header.strip():
            await context.bot.send_message(
                chat_id=user_id,
                text=f"<pre>{message}</pre>",
                parse_mode='HTML',
                reply_markup=reply_markup
            )
    except Exception as e:
        logger.error(f"Ошибка отправки сообщения: {e}")
    
    context.user_data['current_index'] = current_index
    if current_index < len(matched_configs) and not context.user_data.get('stop_sending', False):
        time.sleep(1)
        await send_configs(update, context)
    else:
        if current_index >= len(matched_configs):
            await context.bot.send_message(chat_id=user_id, text="✅ Все конфиги отправлены.")
        return ConversationHandler.END

def is_config_relevant(config: str, target_country: str, country_codes: list, flag_pattern: str = None) -> bool:
    if flag_pattern and re.search(flag_pattern, config, re.IGNORECASE):
        return True
    if detect_by_keywords(config, target_country):
        return True
    domain = extract_domain(config)
    if domain:
        tld = domain.split('.')[-1].lower()
        if tld in country_codes:
            return True
    return False

def strict_config_check(configs: list, target_country: str) -> list:
    valid_configs = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        futures = []
        for config in configs:
            futures.append(executor.submit(validate_config, config, target_country))
        for future in concurrent.futures.as_completed(futures):
            config, is_valid = future.result()
            if is_valid:
                valid_configs.append(config)
    return valid_configs

def validate_config(config: str, target_country: str) -> tuple:
    try:
        host = extract_host(config)
        if not host:
            return (config, False)
        ip = resolve_dns(host)
        if not ip:
            return (config, False)
        country = geolocate_ip(ip)
        if country and country.lower() == target_country:
            return (config, True)
        if not validate_config_structure(config):
            return (config, False)
        if neural_client and len(config) < 500:
            # Создаем новый event loop для асинхронного вызова
            import asyncio
            loop = asyncio.new_event_loop()
            asyncio.set_event_loop(loop)
            try:
                neural_country = loop.run_until_complete(neural_detect_country(config))
                if neural_country and neural_country == target_country:
                    return (config, True)
            except Exception as e:
                logger.error(f"Ошибка нейросети при проверке конфига: {e}")
            finally:
                loop.close()
        return (config, False)
    except Exception as e:
        logger.error(f"Ошибка проверки конфига: {e}")
        return (config, False)

def validate_config_structure(config: str) -> bool:
    if config.startswith('vmess://'):
        try:
            encoded = config.split('://')[1].split('?')[0]
            padding = '=' * (-len(encoded) % 4)
            decoded = base64.b64decode(encoded + padding).decode('utf-8', errors='replace')
            json_data = json.loads(decoded)
            required_fields = ['v', 'ps', 'add', 'port', 'id', 'aid']
            return all(field in json_data for field in required_fields)
        except:
            return False
    elif config.startswith('vless://'):
        pattern = r'vless://[a-f0-9]{8}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{12}@'
        return bool(re.match(pattern, config))
    return bool(re.search(r'\b(?:\d{1,3}\.){3}\d{1,3}:\d+\b', config))

def resolve_dns(host: str) -> str:
    try:
        if re.match(r'\d+\.\d+\.\d+\.\d+', host):
            return host
        return socket.gethostbyname(host)
    except:
        return None

def geolocate_ip(ip: str) -> str:
    try:
        if re.match(r'(10\.|192\.168\.|172\.(1[6-9]|2[0-9]|3[0-1])\.)', ip):
            return None
        response = requests.get(f"{GEOIP_API}{ip}", headers=HEADERS, timeout=5)
        data = response.json()
        if data.get('status') == 'success':
            return data.get('country')
    except Exception as e:
        logger.error(f"Ошибка геолокации для {ip}: {e}")
    return None

def get_country_flag(country_name: str) -> str:
    flag_map = {
        "united states": "🇺🇸",
        "russia": "🇷🇺",
        "germany": "🇩🇪",
        "united kingdom": "🇬🇧",
        "france": "🇫🇷",
        "japan": "🇯🇵",
        "brazil": "🇧🇷",
        "south korea": "🇰🇷",
        "turkey": "🇹🇷",
        "taiwan": "🇹🇼",
        "switzerland": "🇨🇭",
        "china": "🇨🇳",
        "india": "🇮🇳",
        "canada": "🇨🇦",
        "australia": "🇦🇺",
        "singapore": "🇸🇬",
        "italy": "🇮🇹",
        "spain": "🇪🇸",
        "portugal": "🇵🇹",
        "norway": "🇳🇴",
        "finland": "🇫🇮",
        "denmark": "🇩🇰",
        "poland": "🇵🇱",
        "ukraine": "🇺🇦",
        "belarus": "🇧🇾",
        "indonesia": "🇮🇩",
        "malaysia": "🇲🇾",
        "philippines": "🇵🇭",
        "vietnam": "🇻🇳",
        "thailand": "🇹🇭",
        "czech republic": "🇨🇿",
        "romania": "🇷🇴",
        "hungary": "🇭🇺",
        "greece": "🇬🇷",
        "bulgaria": "🇧🇬",
        "egypt": "🇪🇬",
        "nigeria": "🇳🇬",
        "kenya": "🇰🇪",
        "colombia": "🇨🇴",
        "peru": "🇵🇪",
        "chile": "🇨🇱",
        "venezuela": "🇻🇪",
        "austria": "🇦🇹",
        "belgium": "🇧🇪",
        "ireland": "🇮🇪"
    }
    return flag_map.get(country_name.lower(), "")

def get_country_flag_pattern(country_name: str) -> str:
    flag = get_country_flag(country_name)
    if flag:
        return re.escape(flag)
    return ""

def detect_by_keywords(config: str, target_country: str) -> bool:
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
    if target_country in patterns:
        for pattern in patterns[target_country]:
            if re.search(pattern, config, re.IGNORECASE):
                return True
    return False

def extract_host(config: str) -> str:
    if config.startswith(('vmess://', 'vless://')):
        try:
            encoded = config.split('://')[1].split('?')[0]
            padding = '=' * (-len(encoded) % 4)
            decoded = base64.b64decode(encoded + padding).decode('utf-8', errors='replace')
            json_data = json.loads(decoded)
            host = json_data.get('host') or json_data.get('add', '')
            if host:
                return host
        except Exception as e:
            logger.debug(f"Ошибка декодирования VMESS/VLESS: {e}")
    host_match = re.search(r'\b(?:\d{1,3}\.){3}\d{1,3}\b', config)
    if host_match:
        return host_match.group(0)
    domain = extract_domain(config)
    if domain:
        return domain
    return None

def extract_domain(config: str) -> str:
    url_match = re.search(r'(?:https?://)?([a-z0-9.-]+\.[a-z]{2,})', config, re.IGNORECASE)
    if url_match:
        return url_match.group(1)
    domain_match = re.search(r'\b(?:[a-z0-9]+(-[a-z0-9]+)*\.)+[a-z]{2,}\b', config, re.IGNORECASE)
    if domain_match:
        return domain_match.group(0)
    return None

async def cancel(update: Update, context: CallbackContext):
    for key in ['file_path', 'file_paths']:
        if key in context.user_data:
            file_paths = context.user_data[key]
            if not isinstance(file_paths, list):
                file_paths = [file_paths]
            for file_path in file_paths:
                if os.path.exists(file_path):
                    os.unlink(file_path)
            del context.user_data[key]
    context.user_data.clear()
    await update.message.reply_text("Операция отменена.")
    return ConversationHandler.END

def main() -> None:
    # Исправление: создаем приложение без явного указания updater
    application = Application.builder().token(TOKEN).build()

    conv_handler = ConversationHandler(
        entry_points=[CommandHandler("check_configs", check_configs)],
        states={
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
            SENDING_CONFIGS: [
                CallbackQueryHandler(button_handler)
            ]
        },
        fallbacks=[CommandHandler("cancel", cancel)],
        allow_reentry=True,
        per_user=True,
        per_chat=False,
        per_message=False
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
