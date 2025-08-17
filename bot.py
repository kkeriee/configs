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
import asyncio
import random
import concurrent.futures
from collections import OrderedDict
from urllib.parse import urlparse
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup, constants
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
import aiodns
import dns.asyncresolver

# Конфигурация
TOKEN = os.getenv("TELEGRAM_BOT_TOKEN")
NEURAL_API_KEY = os.getenv("NEURAL_API_KEY")
MAX_FILE_SIZE = 15 * 1024 * 1024  # 15MB
MAX_MSG_LENGTH = 4000
MAX_RETRIES = 8
MAX_CONCURRENT_DNS = 50  # Максимальное количество параллельных DNS-запросов
MAX_CONFIGS = 40000  # Максимальное количество конфигураций для обработки
PROGRESS_UPDATE_INTERVAL = 2.0  # Интервал обновления прогресс-бара (секунды)
GEOLOCATION_TIMEOUT = 15.0  # Таймаут для геолокации (секунды)
DNS_TIMEOUT = 8.0  # Таймаут для DNS-запросов (секунды)
CACHE_MAX_SIZE = 5000  # Максимальный размер кэшей
CACHE_TTL = 3600  # Время жизни кэша в секундах
REQUESTS_PER_MINUTE = 5  # Ограничение запросов в минуту

SUPPORTED_PROTOCOLS = {
    'vmess', 'vless', 'trojan', 'ss', 'ssr', 'socks', 'http', 
    'https', 'hysteria', 'hysteria2', 'wg', 'openvpn', 'brook'
}

# URL для скачивания базы геолокации
DB_IP_URL = "https://github.com/Loyalsoldier/geoip/releases/latest/download/Country.mmdb"
DB_SHA256_URL = "https://github.com/Loyalsoldier/geoip/releases/latest/download/Country.mmdb.sha256"

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
        timeout=15
    )
    logger.info("Нейросеть DeepSeek-R1 инициализирована")
else:
    logger.warning("NEURAL_API_KEY не установлен, функции нейросети отключены")

# Инициализация DNS-резолвера
resolver = dns.asyncresolver.Resolver()
resolver.timeout = DNS_TIMEOUT
resolver.lifetime = DNS_TIMEOUT

# Ограничитель запросов
user_request_times = {}

# Кэши с ограничением размера и TTL
class LimitedCache(OrderedDict):
    """Кэш с ограничением размера и временем жизни элементов"""
    def __init__(self, max_size=1000, ttl=3600):
        super().__init__()
        self.max_size = max_size
        self.ttl = ttl
        self.timestamps = {}
    
    def __getitem__(self, key):
        # Проверяем TTL
        if key in self.timestamps and time.time() - self.timestamps[key] > self.ttl:
            self.pop(key, None)
            self.timestamps.pop(key, None)
            raise KeyError(key)
        return super().__getitem__(key)
    
    def __setitem__(self, key, value):
        # Удаляем старые записи, если кэш переполнен
        if len(self) >= self.max_size:
            self.popitem(last=False)
        super().__setitem__(key, value)
        self.timestamps[key] = time.time()
    
    def cleanup(self):
        """Очистка устаревших записей"""
        now = time.time()
        keys_to_remove = [k for k, t in self.timestamps.items() if now - t > self.ttl]
        for k in keys_to_remove:
            self.pop(k, None)
            self.timestamps.pop(k, None)

# Инициализация кэшей с ограничениями
country_cache = LimitedCache(max_size=CACHE_MAX_SIZE, ttl=CACHE_TTL)
geo_cache = LimitedCache(max_size=CACHE_MAX_SIZE, ttl=CACHE_TTL)
dns_cache = LimitedCache(max_size=CACHE_MAX_SIZE, ttl=CACHE_TTL)
config_cache = LimitedCache(max_size=CACHE_MAX_SIZE, ttl=CACHE_TTL)
instruction_cache = LimitedCache(max_size=100, ttl=CACHE_TTL * 2)  # Инструкции живут дольше
country_normalization_cache = LimitedCache(max_size=CACHE_MAX_SIZE, ttl=CACHE_TTL)
neural_improvement_cache = LimitedCache(max_size=100, ttl=CACHE_TTL * 2)

# Инициализация базы геолокации
geoip_reader = None
geoip_file_path = None

def check_rate_limit(user_id: int) -> bool:
    """Проверка ограничения запросов"""
    now = time.time()
    if user_id in user_request_times:
        # Удаляем старые записи
        user_request_times[user_id] = [t for t in user_request_times[user_id] if now - t < 60]
        
        # Проверяем лимит
        if len(user_request_times[user_id]) >= REQUESTS_PER_MINUTE:
            return False
    
    # Добавляем текущий запрос
    if user_id not in user_request_times:
        user_request_times[user_id] = []
    user_request_times[user_id].append(now)
    return True

def initialize_geoip_database_sync():
    """Синхронная инициализация базы геолокации с использованием временного файла"""
    global geoip_reader, geoip_file_path
    
    # Удаляем предыдущий временный файл если существует
    if geoip_file_path and os.path.exists(geoip_file_path):
        try:
            os.unlink(geoip_file_path)
            logger.info(f"Удален старый временный файл: {geoip_file_path}")
        except Exception as e:
            logger.error(f"Ошибка удаления временного файла: {e}")
    
    try:
        logger.info(f"Скачивание базы геолокации: {DB_IP_URL}")
        
        # Скачиваем SHA256 хэш
        sha256 = None
        try:
            sha256_response = requests.get(DB_SHA256_URL, timeout=30)
            if sha256_response.status_code == 200:
                sha256 = sha256_response.text.split()[0]
                logger.info(f"Получен SHA256 хэш: {sha256}")
        except Exception as e:
            logger.warning(f"Не удалось получить SHA256 хэш: {e}")
        
        # Скачиваем базу
        for attempt in range(3):
            try:
                response = requests.get(DB_IP_URL, timeout=60)
                response.raise_for_status()
                
                # Проверяем целостность, если доступен SHA256
                if sha256:
                    import hashlib
                    file_hash = hashlib.sha256(response.content).hexdigest()
                    if file_hash.lower() != sha256.lower():
                        logger.error(f"Ошибка проверки целостности: ожидаемый хэш {sha256}, полученный {file_hash}")
                        continue
                
                # Создаем временный файл
                with tempfile.NamedTemporaryFile(delete=False, suffix='.mmdb') as tmp_file:
                    tmp_file.write(response.content)
                    geoip_file_path = tmp_file.name
                    logger.info(f"Создан временный файл: {geoip_file_path} ({len(response.content)} байт)")
                
                # Загружаем базу из файла
                geoip_reader = maxminddb.open_database(geoip_file_path)
                logger.info("База геолокации успешно загружена")
                return True
            except Exception as e:
                logger.error(f"Ошибка инициализации (попытка {attempt+1}/3): {e}")
                if attempt < 2:
                    time.sleep(2)
        return False
    except Exception as e:
        logger.critical(f"Критическая ошибка инициализации базы: {e}")
        return False

async def initialize_geoip_database():
    """Асинхронная обертка для инициализации базы геолокации"""
    loop = asyncio.get_event_loop()
    return await loop.run_in_executor(None, initialize_geoip_database_sync)

def clear_temporary_data(context: CallbackContext):
    """Очистка временных данных в user_data"""
    keys_to_clear = [
        'matched_configs', 'current_index', 'stop_sending', 
        'strict_in_progress', 'improved_search', 'country_request', 
        'country', 'target_country', 'country_codes', 'search_mode',
        'file_path', 'file_paths', 'progress_last_update', 'progress_message_id'
    ]
    for key in keys_to_clear:
        if key in context.user_data:
            del context.user_data[key]

def normalize_text(text: str) -> str:
    """Нормализация текста страны для поиска"""
    text = text.lower().strip()
    
    # Проверяем кэш
    if text in country_normalization_cache:
        return country_normalization_cache[text]
    
    # Базовая нормализация
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
    
    # Применяем маппинг
    for key, value in ru_en_map.items():
        text = text.replace(key, value)
    
    # Сохраняем в кэш
    country_normalization_cache[text] = text
    return text

async def neural_normalize_country(text: str) -> str:
    """Нормализация страны с помощью нейросети"""
    if not neural_client:
        return None
    
    # Проверяем кэш
    if text in country_cache:
        return country_cache[text]
    
    system_prompt = (
        "Определи страну по тексту. Верни только английское название страны в нижнем регистре. "
        "Примеры: 'рф' → 'russia', 'соединенные штаты' → 'united states'. "
        "Если не уверен, верни None."
    )
    
    try:
        response = neural_client.chat.completions.create(
            model="deepseek/deepseek-r1-0528",
            messages=[
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": text}
            ],
            max_tokens=50,
            temperature=0.1,
            timeout=10.0
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
    
    # Используем хэш конфига для кэширования
    config_hash = hash(config)
    if config_hash in config_cache:
        return config_cache[config_hash]
    
    system_prompt = (
        "Определи страну для этого VPN конфига. Ответь только названием страны на английском в нижнем регистре "
        "или 'unknown', если не удалось определить. Учитывай явные указания страны в названии сервера или комментариях."
    )
    
    try:
        response = neural_client.chat.completions.create(
            model="deepseek/deepseek-r1-0528",
            messages=[
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": config}
            ],
            max_tokens=20,
            temperature=0.1,
            timeout=8.0
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
        return "Инструкции недоступны (нейросеть отключена)"
    
    # Проверяем кэш
    if country in instruction_cache:
        return instruction_cache[country]
    
    system_prompt = (
        f"Ты эксперт по VPN. Сгенерируй краткую инструкцию по использованию VPN для пользователей из {country}. "
        "Инструкция должна быть на русском, понятной и содержать основные шаги. "
        "Максимум 300 символов."
    )
    
    try:
        response = neural_client.chat.completions.create(
            model="deepseek/deepseek-r1-0528",
            messages=[
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": f"Сгенерируй инструкцию для {country}"}
            ],
            max_tokens=300,
            temperature=0.7,
            timeout=15.0
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
    
    # Проверяем кэш
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
            model="deepseek/deepseek-r1-0528",
            messages=[
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": country}
            ],
            response_format={"type": "json_object"},
            max_tokens=200,
            temperature=0.3,
            timeout=10.0
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
    # Проверка ограничения запросов
    if not check_rate_limit(update.message.from_user.id):
        await update.message.reply_text("❌ Слишком много запросов. Пожалуйста, подождите минуту.")
        return ConversationHandler.END
    
    clear_temporary_data(context)
    user_id = update.message.from_user.id
    
    # Проверяем наличие предыдущих данных
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
    """Обработка загруженного файла с потоковой обработкой"""
    user = update.message.from_user
    document = update.message.document
    
    # Проверка MIME-типа
    if not document.mime_type.startswith('text/'):
        await update.message.reply_text("❌ Пожалуйста, загрузите текстовый файл.")
        return ConversationHandler.END
    
    # Проверка размера
    if document.file_size > MAX_FILE_SIZE:
        await update.message.reply_text(
            f"❌ Файл слишком большой. Максимальный размер: {MAX_FILE_SIZE//1024//1024}MB"
        )
        return ConversationHandler.END
    
    # Скачиваем файл
    try:
        file = await context.bot.get_file(document.file_id)
        file_path = os.path.join(tempfile.gettempdir(), f"{document.file_id}.tmp")
        
        # Скачиваем в временный файл
        await file.download_to_drive(file_path)
        
        # Потоковая обработка файла
        configs = []
        current_config = []
        line_count = 0
        max_lines = MAX_CONFIGS * 10  # Ограничение на количество строк
        
        with open(file_path, 'r', encoding='utf-8', errors='replace') as f:
            for line in f:
                line_count += 1
                if line_count > max_lines:
                    break
                
                stripped = line.strip()
                if stripped:
                    # Проверка на начало нового конфига
                    if any(stripped.startswith(proto + "://") for proto in SUPPORTED_PROTOCOLS):
                        if current_config:
                            configs.append("\n".join(current_config))
                            current_config = []
                            # Проверка лимита
                            if len(configs) >= MAX_CONFIGS:
                                break
                    current_config.append(stripped)
            
            # Добавляем последний конфиг
            if current_config and len(configs) < MAX_CONFIGS:
                configs.append("\n".join(current_config))
        
        # Удаляем временный файл
        os.unlink(file_path)
        
        context.user_data['configs'] = configs
        context.user_data['file_name'] = document.file_name
        
        logger.info(f"Пользователь {user.id} загрузил файл: {document.file_name} ({len(configs)} конфигов)")
        
        # Отправляем результат
        if len(configs) == 0:
            await update.message.reply_text("❌ Не найдено ни одной конфигурации в файле.")
            return ConversationHandler.END
            
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
        
    except Exception as e:
        logger.error(f"Ошибка обработки файла: {e}")
        await update.message.reply_text("❌ Произошла ошибка при обработке файла. Попробуйте снова.")
        return ConversationHandler.END

async def button_handler(update: Update, context: CallbackContext) -> int:
    """Обработчик inline кнопок с улучшенной обработкой"""
    query = update.callback_query
    await query.answer()
    
    # Проверка ограничения запросов
    if not check_rate_limit(query.from_user.id):
        await query.edit_message_text("❌ Слишком много запросов. Пожалуйста, подождите минуту.")
        return ConversationHandler.END
    
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
    """Обработка ввода страны с улучшенной проверкой"""
    country_request = update.message.text
    context.user_data['country_request'] = country_request
    
    # Проверка на подозрительные запросы
    if len(country_request) > 50 or not re.match(r'^[\w\s\-.,]+$', country_request):
        await update.message.reply_text("❌ Некорректный запрос. Пожалуйста, введите название страны.")
        return WAITING_COUNTRY
    
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
        
        await update.message.reply_text(
            "❌ Страна не распознана. Пожалуйста, уточните название.\n"
            "Примеры: 'США', 'Германия', 'Japan', 'UK'"
        )
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
    
    # Генерируем инструкции, если их нет в кэше
    if country.name.lower() not in instruction_cache:
        instructions = await generate_country_instructions(country.name)
        instruction_cache[country.name.lower()] = instructions
    
    await update.message.reply_text(
        f"🌍 Вы выбрали страну: {country.name}\n"
        f"ℹ️ {instruction_cache.get(country.name.lower(), 'Инструкция генерируется...')}\n"
        "Выберите режим поиска:",
        reply_markup=reply_markup
    )
    return WAITING_MODE

async def fast_search(update: Update, context: CallbackContext):
    """Быстрый поиск конфигов с улучшенной обработкой"""
    user_id = update.callback_query.from_user.id if update.callback_query else update.message.from_user.id
    configs = context.user_data.get('configs', [])
    target_country = context.user_data.get('target_country', '')
    
    if not configs or not target_country:
        await context.bot.send_message(chat_id=user_id, text="❌ Ошибка: данные для поиска отсутствуют.")
        return ConversationHandler.END
    
    start_time = time.time()
    matched_configs = []
    progress_msg = await context.bot.send_message(chat_id=user_id, text="🔎 Начинаю быстрый поиск...")
    
    # Получаем улучшенные параметры поиска
    improved_search = context.user_data.get('improved_search', {})
    additional_keywords = improved_search.get('keywords', [])
    additional_patterns = improved_search.get('patterns', [])
    
    total_configs = len(configs)
    processed = 0
    
    # Создаем индикатор активности
    context.user_data['progress_last_update'] = time.time()
    context.user_data['progress_message_id'] = progress_msg.message_id
    
    try:
        # Обрабатываем конфиги с регулярным обновлением прогресса
        for i, config in enumerate(configs):
            if context.user_data.get('stop_sending'):
                break
                
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
            
            processed += 1
            
            # Регулярное обновление прогресса
            if time.time() - context.user_data.get('progress_last_update', 0) > PROGRESS_UPDATE_INTERVAL or i == total_configs - 1:
                progress = min(processed / total_configs * 100, 100)
                progress_bar = create_progress_bar(progress)
                await context.bot.edit_message_text(
                    chat_id=user_id,
                    message_id=progress_msg.message_id,
                    text=f"🔎 Быстрый поиск: {progress_bar} {progress:.1f}%\nОбработано: {processed}/{total_configs}"
                )
                context.user_data['progress_last_update'] = time.time()
                
                # Проверка необходимости остановки
                if context.user_data.get('stop_sending'):
                    break
        
        logger.info(f"Найдено {len(matched_configs)} конфигов для {context.user_data['country']}, обработка заняла {time.time()-start_time:.2f} сек")
        
        if not matched_configs:
            await context.bot.edit_message_text(
                chat_id=user_id,
                message_id=progress_msg.message_id,
                text=f"❌ Конфигурации для {context.user_data['country']} не найдены."
            )
            return ConversationHandler.END
        
        context.user_data['matched_configs'] = matched_configs
        
        # Обновляем сообщение с результатом
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
        
    except Exception as e:
        logger.error(f"Ошибка быстрого поиска: {e}")
        await context.bot.edit_message_text(
            chat_id=user_id,
            message_id=progress_msg.message_id,
            text="❌ Произошла ошибка при поиске конфигураций."
        )
        return ConversationHandler.END

async def resolve_dns_async(host: str) -> str:
    """Асинхронное разрешение DNS с кэшированием и повторными попытками"""
    if host in dns_cache:
        return dns_cache[host]
    
    try:
        if re.match(r'^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$', host):
            ip = host
            dns_cache[host] = ip
            return ip
        
        # Асинхронный DNS-запрос
        try:
            result = await resolver.resolve(host, 'A')
            ip = result[0].to_text()
            dns_cache[host] = ip
            return ip
        except Exception as e:
            logger.debug(f"Ошибка асинхронного DNS-запроса для {host}: {e}")
            # Попробуем стандартный метод как fallback
            for attempt in range(MAX_RETRIES):
                try:
                    ip = socket.gethostbyname_ex(host)[-1][0]
                    dns_cache[host] = ip
                    return ip
                except (socket.gaierror, socket.timeout):
                    if attempt < MAX_RETRIES - 1:
                        delay = 2 ** attempt
                        await asyncio.sleep(delay)
                    else:
                        raise
    except Exception as e:
        logger.error(f"Ошибка разрешения DNS для {host}: {e}")
        dns_cache[host] = None
        return None

async def geolocate_ip_async(ip: str) -> str:
    """Асинхронная геолокация IP с использованием локальной базы данных"""
    if not geoip_reader:
        logger.error("Попытка геолокации без инициализированной базы")
        return None
    
    if ip in geo_cache:
        return geo_cache[ip]
    
    try:
        # Пропускаем приватные IP
        if re.match(r'(^127\.)|(^10\.)|(^172\.1[6-9]\.)|(^172\.2[0-9]\.)|(^172\.3[0-1]\.)|(^192\.168\.)', ip):
            geo_cache[ip] = None
            return None
        
        try:
            # Выполняем в отдельном потоке, чтобы не блокировать асинхронный цикл
            loop = asyncio.get_event_loop()
            data = await loop.run_in_executor(None, geoip_reader.get, ip)
            
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

async def strict_search(update: Update, context: CallbackContext):
    """Строгий поиск конфигов с проверкой геолокации и улучшенной обработкой"""
    user_id = update.callback_query.from_user.id if update.callback_query else update.message.from_user.id
    configs = context.user_data.get('configs', [])
    target_country = context.user_data.get('target_country', '')
    
    if not configs or not target_country:
        await context.bot.send_message(chat_id=user_id, text="❌ Ошибка: данные для поиска отсутствуют.")
        return ConversationHandler.END
    
    # Проверка и инициализация базы геолокации
    if not geoip_reader:
        logger.warning("База геолокации не загружена, пытаемся инициализировать...")
        if not await initialize_geoip_database():
            await context.bot.send_message(chat_id=user_id, text="❌ База геолокации недоступна. Строгий поиск невозможен.")
            return ConversationHandler.END
    
    start_time = time.time()
    prelim_configs = []
    progress_msg = await context.bot.send_message(chat_id=user_id, text="🔎 Этап 1: предварительная фильтрация...")
    
    # Получаем улучшенные параметры поиска
    improved_search = context.user_data.get('improved_search', {})
    additional_keywords = improved_search.get('keywords', [])
    additional_patterns = improved_search.get('patterns', [])
    
    total_configs = len(configs)
    processed = 0
    
    try:
        # Предварительная фильтрация
        for i, config in enumerate(configs):
            if context.user_data.get('stop_strict_search'):
                break
                
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
            
            processed += 1
            
            # Регулярное обновление прогресса
            if time.time() - context.user_data.get('progress_last_update', 0) > PROGRESS_UPDATE_INTERVAL or i == total_configs - 1:
                progress = min(processed / total_configs * 100, 100)
                progress_bar = create_progress_bar(progress)
                await context.bot.edit_message_text(
                    chat_id=user_id,
                    message_id=progress_msg.message_id,
                    text=f"🔎 Этап 1: {progress_bar} {progress:.1f}%\nОбработано: {processed}/{total_configs}"
                )
                context.user_data['progress_last_update'] = time.time()
                
                # Проверка необходимости остановки
                if context.user_data.get('stop_strict_search'):
                    break
        
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
        
        # Кнопка остановки
        stop_keyboard = [[InlineKeyboardButton("⏹ Остановить строгий поиск", callback_data='stop_strict_search')]]
        stop_reply_markup = InlineKeyboardMarkup(stop_keyboard)
        
        await context.bot.edit_message_text(
            chat_id=user_id,
            message_id=progress_msg.message_id,
            text=f"🌐 Начинаю проверку геолокации для {total_hosts} уникальных хостов...",
            reply_markup=stop_reply_markup
        )
        
        context.user_data['strict_in_progress'] = True
        context.user_data['progress_last_update'] = time.time()
        context.user_data['progress_message_id'] = progress_msg.message_id
        
        # Проверка геолокации для уникальных хостов с параллельной обработкой
        host_country_map = {}
        total_processed = 0
        stop_search = False
        
        # Создаем семафор для ограничения параллельных запросов
        semaphore = asyncio.Semaphore(MAX_CONCURRENT_DNS)
        
        async def process_host(host):
            nonlocal total_processed
            
            async with semaphore:
                if context.user_data.get('stop_strict_search'):
                    return None, None
                
                try:
                    # Разрешаем DNS
                    ip = await resolve_dns_async(host)
                    
                    # Получаем геолокацию
                    country = None
                    if ip:
                        country = await geolocate_ip_async(ip)
                    
                    # Обновляем прогресс
                    total_processed += 1
                    return host, country
                except Exception as e:
                    logger.error(f"Ошибка обработки хоста {host}: {e}")
                    total_processed += 1
                    return host, None
        
        # Запускаем параллельную обработку
        tasks = [process_host(host) for host in unique_hosts]
        results = []
        
        # Обрабатываем результаты по мере их поступления
        for coro in asyncio.as_completed(tasks):
            try:
                host, country = await asyncio.wait_for(coro, timeout=GEOLOCATION_TIMEOUT)
                if host and country is not None:
                    host_country_map[host] = country
                
                # Обновление прогресса
                if total_processed % 5 == 0 or total_processed == total_hosts:
                    if time.time() - context.user_data.get('progress_last_update', 0) > PROGRESS_UPDATE_INTERVAL:
                        progress = total_processed / total_hosts * 100
                        progress_bar = create_progress_bar(progress)
                        try:
                            await context.bot.edit_message_text(
                                chat_id=user_id,
                                message_id=progress_msg.message_id,
                                text=f"🌐 Этап 2: {progress_bar} {progress:.1f}%\nОбработано хостов: {total_processed}/{total_hosts}",
                                reply_markup=stop_reply_markup
                            )
                            context.user_data['progress_last_update'] = time.time()
                        except Exception as e:
                            logger.debug(f"Ошибка обновления прогресса: {e}")
                
                # Проверка необходимости остановки
                if context.user_data.get('stop_strict_search'):
                    stop_search = True
                    break
            except asyncio.TimeoutError:
                logger.warning(f"Таймаут обработки хоста")
                total_processed += 1
            except Exception as e:
                logger.error(f"Ошибка в цикле обработки: {e}")
                total_processed += 1
        
        # Сбор валидных конфигов
        valid_configs = []
        for host in unique_hosts:
            if context.user_data.get('stop_strict_search'):
                break
                
            country = host_country_map.get(host)
            if country and country.lower() == target_country.lower():
                valid_configs.extend(host_to_configs[host])
        
        total_time = time.time() - start_time
        context.user_data['strict_in_progress'] = False
        
        # Отправляем результат
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
                text=f"✅ Строгий поиск завершен за {total_time:.2f} сек. Найдено {len(valid_configs)} конфигов."
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
        
    except Exception as e:
        logger.error(f"Ошибка строгого поиска: {e}", exc_info=True)
        context.user_data['strict_in_progress'] = False
        await context.bot.edit_message_text(
            chat_id=user_id,
            message_id=progress_msg.message_id,
            text="❌ Произошла ошибка при строгом поиске конфигураций."
        )
        return ConversationHandler.END

async def handle_number(update: Update, context: CallbackContext):
    """Обработка ввода количества конфигов с улучшенной проверкой"""
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
        
        # Перемешиваем и выбираем конфиги
        random.shuffle(matched_configs)
        selected_configs = matched_configs[:num]
        
        context.user_data['matched_configs'] = selected_configs
        context.user_data['current_index'] = 0
        context.user_data['stop_sending'] = False
        context.user_data['progress_last_update'] = time.time()
        
        await update.message.reply_text(f"⏫ Начинаю отправку {num} конфигов...")
        await send_configs(update, context)
        return SENDING_CONFIGS
    except ValueError:
        await update.message.reply_text("❌ Пожалуйста, введите число.")
        return WAITING_NUMBER
    except Exception as e:
        logger.error(f"Ошибка обработки количества конфигов: {e}")
        await update.message.reply_text("❌ Произошла ошибка при обработке запроса.")
        return ConversationHandler.END

async def send_configs(update: Update, context: CallbackContext):
    """Отправка конфигов пользователю с улучшенной обработкой"""
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
    
    # Подготавливаем сообщения
    header = f"Конфиги для {country_name}:\n"
    messages = []
    current_message = header
    
    for config in matched_configs:
        config_line = f"{config}\n"
        if len(current_message) + len(config_line) > MAX_MSG_LENGTH:
            messages.append(current_message)
            current_message = config_line
        else:
            current_message += config_line
    
    if current_message:
        messages.append(current_message)
    
    total_messages = len(messages)
    
    # Отправляем сообщения
    for i, message in enumerate(messages):
        if context.user_data.get('stop_sending'):
            await context.bot.send_message(chat_id=user_id, text="⏹ Отправка остановлена.")
            return ConversationHandler.END
        
        try:
            # Добавляем прогресс в последнее сообщение
            if i == total_messages - 1:
                progress = f"\n⌛ Отправлено {i+1}/{total_messages} сообщений"
                if len(message) + len(progress) <= MAX_MSG_LENGTH:
                    message += progress
            
            # Отправляем сообщение
            await context.bot.send_message(
                chat_id=user_id,
                text=f"<pre>{message}</pre>",
                parse_mode='HTML'
            )
            
            # Задержка между сообщениями
            await asyncio.sleep(0.3)
        except Exception as e:
            logger.error(f"Ошибка отправки сообщения: {e}")
            # Пробуем отправить как обычный текст, если HTML не работает
            try:
                await context.bot.send_message(
                    chat_id=user_id,
                    text=message[:MAX_MSG_LENGTH],
                    parse_mode=None
                )
            except Exception as e2:
                logger.error(f"Ошибка отправки текстового сообщения: {e2}")
    
    await context.bot.send_message(chat_id=user_id, text="✅ Все конфиги отправлены.")
    context.user_data['last_country'] = context.user_data['country']
    clear_temporary_data(context)
    return ConversationHandler.END

def create_progress_bar(progress: float, length: int = 20) -> str:
    """Создает текстовый прогресс-бар с улучшенной отрисовкой"""
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
    """Проверка релевантности конфига с оптимизированным поиском"""
    # Проверяем по ключевым словам
    if detect_by_keywords(config, target_country, additional_keywords, additional_patterns):
        return True
    
    # Проверяем по домену
    domain = extract_domain(config)
    if domain:
        tld = domain.split('.')[-1].lower()
        if tld in country_codes:
            return True
    
    return False

def detect_by_keywords(
    config: str, 
    target_country: str,
    additional_keywords: list = [],
    additional_patterns: list = []
) -> bool:
    """Обнаружение страны по ключевым словам с оптимизированным поиском"""
    # Стандартные паттерны
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
        'philippines': [r'philippines', r'manila', r'\.ph\b', r'菲律宾', r'马尼ла'],
        'vietnam': [r'vietnam', r'hanoi', r'\.vn\b', r'越南', r'河内'],
        'thailand': [r'thailand', r'bangkok', r'\.th\b', r'泰国', r'曼谷'],
        'czech republic': [r'czech', r'prague', r'\.cz\b', r'捷克', r'布拉格'],
        'romania': [r'romania', r'bucharest', r'\.ro\b', r'罗马尼亚', r'布加勒斯特'],
        'hungary': [r'hungary', r'budapest', r'\.hu\b', r'匈牙利', r'布达佩с'],
        'greece': [r'greece', r'athens', r'\.gr\b', r'希腊', r'雅典'],
        'bulgaria': [r'bulgaria', r'sofia', r'\.bg\b', r'保加利亚', r'索非а'],
        'egypt': [r'egypt', r'cairo', r'\.eg\b', r'埃及', r'开罗'],
        'nigeria': [r'nigeria', r'abuja', r'\.ng\b', r'尼日利亚', r'阿布贾'],
        'kenya': [r'kenya', r'nairobi', r'\.ke\b', r'肯尼亚', r'内罗毕'],
        'colombia': [r'colombia', r'bogota', r'\.co\b', r'哥伦比亚', r'波哥大'],
        'peru': [r'peru', r'lima', r'\.pe\b', r'秘鲁', r'利马'],
        'chile': [r'chile', r'santiago', r'\.cl\b', r'智利', r'圣地亚哥'],
        'venezuela': [r'venezuela', r'caracas', r'\.ve\b', r'委内瑞拉', r'加拉加斯'],
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
        "serbia": [r'serbia', r'belgrade', r'\.rs\b', r'塞尔维я'],
        "slovakia": [r'slovakia', r'bratislava', r'\.sk\b', r'斯洛伐克'],
        "slovenia": [r'slovenia', r'ljubljana', r'\.si\b', r'斯洛文尼亚'],
        "sudan": [r'sudan', r'khartoum', r'\.sd\b', r'苏丹'],
        "syria": [r'syria', r'damascus', r'\.sy\b', r'叙利亚'],
        "tunisia": [r'tunisia', r'tunis', r'\.tn\b', r'突尼斯'],
        "uruguay": [r'uruguay', r'montevideo', r'\.uy\b', r'乌拉圭'],
        "uzbekistan": [r'uzbekistan', r'tashkent', r'\.uz\b', r'乌兹бекстан'],
        "yemen": [r'yemen', r'sanaa', r'\.ye\b', r'也门']
    }
    
    # Добавляем улучшенные ключевые слова
    if target_country in patterns:
        patterns[target_country].extend(additional_keywords)
        patterns[target_country].extend(additional_patterns)
    
    # Быстрая проверка по ключевым словам
    if target_country in patterns:
        config_lower = config.lower()
        for pattern in patterns[target_country]:
            if re.search(pattern, config_lower):
                return True
    
    return False

def extract_host(config: str) -> str:
    """Извлечение хоста из конфига с улучшенными паттернами и безопасной обработкой"""
    try:
        # VMess
        if config.startswith('vmess://'):
            try:
                encoded = config.split('://')[1].split('?')[0]
                padding = '=' * (-len(encoded) % 4)
                decoded = base64.b64decode(encoded + padding).decode('utf-8', errors='replace')
                json_data = json.loads(decoded)
                return json_data.get('host') or json_data.get('add', '')
            except Exception as e:
                logger.debug(f"Ошибка декодирования VMess: {e}")
                # Альтернативное извлечение
                match = re.search(r'(?:"add"\\s*:\\s*")([^"]+)', config)
                if match:
                    return match.group(1)
                return None
        
        # VLESS/Trojan
        elif config.startswith(('vless://', 'trojan://')):
            try:
                parsed = urlparse(config)
                return parsed.hostname
            except Exception as e:
                logger.debug(f"Ошибка парсинга VLESS/Trojan: {e}")
                return None
        
        # Shadowsocks
        elif config.startswith('ss://'):
            try:
                parts = config.split('@')
                if len(parts) < 2:
                    return None
                host_port = parts[1].split('#')[0].split('/')[0]
                return host_port.split(':')[0]
            except Exception as e:
                logger.debug(f"Ошибка парсинга Shadowsocks: {e}")
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
                decoded = base64.b64decode(encoded + padding).decode('utf-8', errors='replace')
                parts = decoded.split(':')
                if len(parts) > 2:
                    return parts[0]
            except Exception as e:
                logger.debug(f"Ошибка декодирования SSR: {e}")
                return None
        
        # SOCKS5/HTTP/HTTPS/Hysteria/Hysteria2/Brook
        elif any(config.startswith(proto) for proto in [
            'socks5://', 'http://', 'https://', 
            'hysteria://', 'hysteria2://', 'brook://'
        ]):
            try:
                parsed = urlparse(config)
                return parsed.hostname
            except Exception as e:
                logger.debug(f"Ошибка парсинга протокола: {e}")
                return None
        
        # WireGuard
        elif '[Interface]' in config and '[Peer]' in config:
            try:
                match = re.search(r'Endpoint\s*=\s*([\w.-]+):', config)
                return match.group(1) if match else None
            except Exception as e:
                logger.debug(f"Ошибка парсинга WireGuard: {e}")
                return None
        
        # OpenVPN
        elif 'openvpn' in config.lower():
            try:
                match = re.search(r'remote\s+([\w.-]+)\s+\d+', config)
                return match.group(1) if match else None
            except Exception as e:
                logger.debug(f"Ошибка парсинга OpenVPN: {e}")
                return None
        
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
    """Извлечение домена из конфига с безопасной обработкой"""
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
    """Отмена операции и очистка с улучшенной обработкой"""
    global geoip_file_path
    
    # Очистка временных данных пользователя
    clear_temporary_data(context)
    
    # Удаление временного файла базы геолокации
    if geoip_file_path and os.path.exists(geoip_file_path):
        try:
            os.unlink(geoip_file_path)
            logger.info(f"Временный файл базы удален: {geoip_file_path}")
            geoip_file_path = None
        except Exception as e:
            logger.error(f"Ошибка удаления временного файла: {e}")
    
    # Очистка кэшей
    country_cache.cleanup()
    geo_cache.cleanup()
    dns_cache.cleanup()
    config_cache.cleanup()
    instruction_cache.cleanup()
    country_normalization_cache.cleanup()
    neural_improvement_cache.cleanup()
    
    await update.message.reply_text("Операция отменена.")
    return ConversationHandler.END

async def post_init(application: Application):
    """Инициализация после запуска приложения с улучшенной обработкой ошибок"""
    try:
        logger.info("Инициализация базы геолокации...")
        if not await initialize_geoip_database():
            logger.error("Не удалось загрузить базу геолокации. Строгий поиск будет недоступен")
        else:
            logger.info("База геолокации успешно загружена")
    except Exception as e:
        logger.error(f"Ошибка при инициализации базы геолокации: {e}", exc_info=True)

def main() -> None:
    """Основная функция запуска бота с улучшенной обработкой"""
    application = Application.builder().token(TOKEN).post_init(post_init).build()
    
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
    
    # Добавляем обработчик ошибок
    async def error_handler(update: object, context: CallbackContext) -> None:
        """Обработчик ошибок с подробным логированием"""
        logger.error("Exception while handling an update:", exc_info=context.error)
        if update and hasattr(update, 'message'):
            try:
                await update.message.reply_text("❌ Произошла ошибка при обработке запроса. Попробуйте снова позже.")
            except:
                pass
    
    application.add_error_handler(error_handler)
    
    # Определяем режим запуска
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
