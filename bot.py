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
import io
import gzip
import threading
import hashlib
from http.server import BaseHTTPRequestHandler, HTTPServer
from datetime import datetime, timedelta, UTC
from collections import OrderedDict
from urllib.parse import urlparse
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import (
    Application,
    CommandHandler,
    MessageHandler,
    filters,
    ConversationHandler,
    CallbackQueryHandler,
    CallbackContext,
    ContextTypes
)
import maxminddb
import dns.asyncresolver
import dns.resolver
import dns.exception

# Импортируем данные о странах из отдельного файла
from country_data import (
    FLAG_COUNTRY_MAP, 
    COUNTRY_PATTERNS, 
    COUNTRY_INSTRUCTIONS,
    get_country_code,
    normalize_country_name
)

# Настройка логирования
logging.basicConfig(
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    level=logging.INFO
)
logger = logging.getLogger(__name__)

# Конфигурация
TOKEN = os.getenv("TELEGRAM_BOT_TOKEN")
MAX_FILE_SIZE = 15 * 1024 * 1024  # 15MB
MAX_MSG_LENGTH = 4000
MAX_CONCURRENT_DNS = 50  # Максимальное количество параллельных DNS-запросов
MAX_CONFIGS = 40000  # Максимальное количество конфигураций для обработки
PROGRESS_UPDATE_INTERVAL = 2.0  # Интервал обновления прогресс-бара (секунды)
GEOLOCATION_TIMEOUT = 15.0  # Таймаут для геолокации (секунды)
DNS_TIMEOUT = 15.0  # Увеличенный таймаут для DNS-запросов
CACHE_MAX_SIZE = 5000  # Максимальный размер кэшей
CACHE_TTL = 3600  # Время жизни кэша в секундах
PORT = int(os.environ.get('PORT', 8080))  # Порт для Render
WEBHOOK_URL = os.getenv("RENDER_EXTERNAL_URL", "") + f"/{TOKEN}"  # URL для вебхука

# Состояния разговора
START, WAITING_FILE, WAITING_COUNTRY, WAITING_NUMBER = range(4)

# Поддерживаемые протоколы (расширенный список)
SUPPORTED_PROTOCOLS = [
    'vmess', 'vless', 'trojan', 'ss', 'ssr', 'socks', 'http', 'https',
    'ss://', 'trojan-go://', 'snell://', 'hy2://', 'tuic://', 'wireguard://',
    'hysteria://', 'hysteria2://', 'naive://', 'wg://', 'brook://'
]

# Глобальные переменные для геолокации
geoip_file_path = None
geoip_db = None
geoip_db_lock = asyncio.Lock()

# Глобальные переменные для приложения и event loop
app = None
loop = None

# Предварительно скомпилированные регулярные выражения
DOMAIN_PATTERN = re.compile(r'(?:[a-z0-9](?:[a-z0-9-]{0,61}[a-z0-9])?\.)+[a-z]{2,}', re.IGNORECASE)
IPV4_PATTERN = re.compile(r'\b(?:\d{1,3}\.){3}\d{1,3}\b')
HOST_PATTERNS = [
    re.compile(r'@([\w\.-]+):?', re.IGNORECASE),
    re.compile(r'host\s*[:=]\s*"([^"]+)"', re.IGNORECASE),
    re.compile(r'address\s*=\s*([\w\.-]+)', re.IGNORECASE),
    re.compile(r'server\s*=\s*([\w\.-]+)', re.IGNORECASE),
    re.compile(r'hostname\s*=\s*([\w\.-]+)', re.IGNORECASE)
]

# Кэши для DNS и геолокации
dns_cache = OrderedDict()
geo_cache = OrderedDict()

# Класс для обработки HTTP запросов (вебхуки + health check)
class WebhookHandler(BaseHTTPRequestHandler):
    def do_GET(self):
        if self.path == '/':
            self.send_response(200)
            self.end_headers()
            self.wfile.write(b'OK')
        else:
            self.send_response(404)
            self.end_headers()
            
    def do_POST(self):
        global app, loop
        if self.path == f'/{TOKEN}':
            content_length = int(self.headers['Content-Length'])
            post_data = self.rfile.read(content_length)
            # Обработка вебхука в основном event loop
            if app and loop:
                update = Update.de_json(json.loads(post_data.decode('utf-8')), app.bot)
                asyncio.run_coroutine_threadsafe(
                    app.process_update(update), 
                    loop
                )
            self.send_response(200)
            self.end_headers()
            self.wfile.write(b'OK')
        else:
            self.send_response(404)
            self.end_headers()

def run_http_server():
    """Запуск HTTP сервера для вебхуков и health check"""
    server = HTTPServer(('0.0.0.0', PORT), WebhookHandler)
    logger.info(f"HTTP сервер запущен на порту {PORT}")
    server.serve_forever()

def clear_temporary_data(context: CallbackContext):
    """Очистка временных данных в user_data"""
    keys_to_clear = [
        'matched_configs', 'current_index', 'stop_sending',
        'strict_in_progress', 'stop_strict_search', 'progress_message_id',
        'progress_last_update', 'stop_simple_search', 'simple_search_in_progress',
        'country_request', 'country', 'target_country', 'country_codes',
        'search_mode', 'file_path', 'file_paths', 'configs', 'file_name', 'last_country'
    ]
    for key in keys_to_clear:
        if key in context.user_data:
            del context.user_data[key]

def create_progress_bar(progress: float, length: int = 20) -> str:
    """Создает текстовый прогресс-бар с улучшенной отрисовкой"""
    filled = int(progress / 100 * length)
    empty = length - filled
    return '█' * filled + '░' * empty

def is_config_relevant(config: str, target_country: str, country_codes: list) -> bool:
    """
    Проверка релевантности конфига с оптимизированным поиском
    """
    config_lower = config.lower()
    
    # Убедимся, что country_codes - это список
    if not isinstance(country_codes, list):
        country_codes = []
    
    # Проверяем по домену и TLD
    domain = extract_domain(config)
    if domain:
        # Проверка TLD
        tld = domain.split('.')[-1].lower()
        if tld in country_codes:
            logger.debug(f"Конфиг релевантен по TLD: {tld}")
            return True
        
        # Проверка ключевых слов в домене
        normalized_target = normalize_country_name(target_country)
        if normalized_target in COUNTRY_PATTERNS:
            for pattern in COUNTRY_PATTERNS[normalized_target]:
                if re.search(pattern, domain):
                    logger.debug(f"Конфиг релевантен по ключевому слову в домене: {pattern}")
                    return True
    
    # Проверяем по ключевым словам с нормализацией целевой страны
    return detect_by_keywords(config_lower, target_country)

def detect_by_keywords(config_lower: str, target_country: str) -> bool:
    """
    Обнаружение страны по ключевым словам
    """
    # Нормализуем целевую страну к формату, используемому в COUNTRY_PATTERNS
    normalized_target = normalize_country_name(target_country)
    
    # Проверяем, существует ли такая страна в наших данных
    if normalized_target not in COUNTRY_PATTERNS:
        logger.warning(f"Страна '{target_country}' не найдена в COUNTRY_PATTERNS. Нормализовано как: '{normalized_target}'")
        return False
    
    # Проверяем паттерны для нормализованной страны
    for pattern in COUNTRY_PATTERNS[normalized_target]:
        if re.search(pattern, config_lower):
            logger.debug(f"Найдено соответствие по ключевому слову: {pattern}")
            return True
    
    return False

def extract_host(config: str) -> str:
    """Извлечение хоста из конфига с улучшенными паттернами и безопасной обработкой"""
    try:
        # VMess
        if config.startswith('vmess://'):
            try:
                encoded = config.split('://')[1].split('?')[0]
                # Добавляем padding для корректного декодирования base64
                padding = '=' * (-len(encoded) % 4)
                decoded = base64.b64decode(encoded + padding).decode('utf-8', errors='replace')
                json_data = json.loads(decoded)
                return json_data.get('host') or json_data.get('add', '')
            except Exception as e:
                logger.debug(f"Ошибка декодирования VMess: {e}")
                return None
        
        # VLESS
        if config.startswith('vless://'):
            try:
                # Извлечение хоста из URL
                url_part = config.split('://')[1].split('?')[0]
                if '@' not in url_part:
                    return None
                host = url_part.split('@')[1].split(':')[0]
                return host
            except Exception as e:
                logger.debug(f"Ошибка обработки VLESS: {e}")
                return None
        
        # Trojan
        if config.startswith('trojan://') or config.startswith('trojan-go://'):
            try:
                # Извлечение хоста из URL
                url_part = config.split('://')[1].split('?')[0]
                if '@' not in url_part:
                    return None
                host = url_part.split('@')[1].split(':')[0]
                return host
            except Exception as e:
                logger.debug(f"Ошибка обработки Trojan: {e}")
                return None
        
        # Shadowsocks
        if config.startswith('ss://'):
            try:
                # Удалить префикс
                url = config.split('://')[1]
                # Проверка на наличие @ (userinfo)
                if '@' in url:
                    # Формат: метод:пароль@хост:порт
                    userinfo, hostport = url.split('@', 1)
                    host = hostport.split(':')[0]
                    return host
                else:
                    # Base64 формат
                    decoded = base64.b64decode(url.split('#')[0] + '==').decode('utf-8', errors='replace')
                    if '@' in decoded:
                        host = decoded.split('@')[1].split(':')[0]
                        return host
                    else:
                        # Формат: host:port
                        parts = decoded.split(':')
                        if len(parts) >= 2:
                            return parts[0]
            except Exception as e:
                logger.debug(f"Ошибка обработки Shadowsocks: {e}")
                return None
        
        # Wireguard
        if config.startswith('wg://') or config.startswith('wireguard://'):
            try:
                # Извлечение хоста из URL
                url_part = config.split('://')[1].split('?')[0]
                if '@' not in url_part:
                    return None
                host = url_part.split('@')[1].split(':')[0]
                return host
            except Exception as e:
                logger.debug(f"Ошибка обработки Wireguard: {e}")
                return None
        
        # Общий случай - используем предварительно скомпилированные паттерны
        for pattern in HOST_PATTERNS:
            match = pattern.search(config)
            if match and match.lastindex:
                host = match.group(1)
                # Проверка, что извлечено что-то осмысленное
                if len(host) > 3 and '.' in host:
                    return host
                
        # Проверка IPv4
        ipv4_match = IPV4_PATTERN.search(config)
        if ipv4_match:
            return ipv4_match.group(0)
                
    except Exception as e:
        logger.debug(f"Ошибка извлечения хоста: {e}")
    return None

def extract_domain(config: str) -> str:
    """Извлечение домена из конфига с безопасной обработкой"""
    try:
        match = DOMAIN_PATTERN.search(config)
        if match:
            return match.group(0).lower()
    except Exception as e:
        logger.debug(f"Ошибка извлечения домена: {e}")
    return None

def calculate_config_hash(config: str) -> str:
    """Вычисление хеша SHA256 для конфига"""
    return hashlib.sha256(config.encode('utf-8')).hexdigest()

async def generate_country_instructions(country: str) -> str:
    """Генерация инструкций для страны"""
    return COUNTRY_INSTRUCTIONS.get(country.lower(), f"Инструкция по настройке для {country}")

async def start_check(update: Update, context: CallbackContext):
    """Начало проверки конфигов с выбором действия"""
    # Проверка ограничения запросов для всех пользователей, кроме исключения
    if update.message.from_user.id != 1040929628 and not check_rate_limit(update.message.from_user.id, context):
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
            f"Обнаружен предыдущий файл: {context.user_data['file_name']}\n"
            f"Последняя страна: {context.user_data['last_country']}\n"
            "Выберите действие:",
            reply_markup=reply_markup
        )
        return START
    else:
        await update.message.reply_text(
            "📎 Пожалуйста, загрузите файл с конфигурациями.\n"
            "Поддерживаются текстовые файлы с конфигурациями (макс. 15MB)."
        )
        return WAITING_FILE

# Новая функция для принудительного сброса состояния
async def force_start_check(update: Update, context: CallbackContext):
    """Начало проверки конфигов с принудительным запросом нового файла"""
    # Проверка ограничения запросов для всех пользователей, кроме исключения
    if update.message.from_user.id != 1040929628 and not check_rate_limit(update.message.from_user.id, context):
        await update.message.reply_text("❌ Слишком много запросов. Пожалуйста, подождите минуту.")
        return ConversationHandler.END
    
    # Принудительно очищаем все данные пользователя
    clear_temporary_data(context)
    
    # Запрашиваем новый файл
    await update.message.reply_text(
        "📎 Пожалуйста, загрузите файл с конфигурациями.\n"
        "Поддерживаются текстовые файлы с конфигурациями (макс. 15MB)."
    )
    return WAITING_FILE

async def handle_file(update: Update, context: CallbackContext):
    """Обработка загруженного файла с конфигурациями"""
    document = update.message.document
    user = update.message.from_user
    
    # Проверка размера файла
    if document.file_size > MAX_FILE_SIZE:
        await update.message.reply_text(
            f"❌ Файл слишком большой! Максимальный размер: {MAX_FILE_SIZE/(1024*1024)}MB"
        )
        return WAITING_FILE
    
    # Скачивание файла
    try:
        file = await context.bot.get_file(document.file_id)
        file_path = os.path.join(tempfile.gettempdir(), document.file_name)
        await file.download_to_drive(file_path)
    except Exception as e:
        logger.error(f"Ошибка загрузки файла: {e}")
        await update.message.reply_text("❌ Ошибка при загрузке файла. Попробуйте еще раз.")
        return WAITING_FILE
    
    # Обработка содержимого файла
    try:
        with open(file_path, 'r', encoding='utf-8', errors='replace') as f:
            content = f.read()
        
        # Извлечение конфигураций
        configs = extract_configs(content)
        
        # Удаляем временный файл
        os.unlink(file_path)
        
        if len(configs) > MAX_CONFIGS:
            configs = configs[:MAX_CONFIGS]
            logger.warning(f"Файл содержит слишком много конфигов. Ограничено до {MAX_CONFIGS}")
        
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
        return START
        
    except Exception as e:
        logger.error(f"Ошибка обработки файла: {e}", exc_info=True)
        try:
            os.unlink(file_path)
        except:
            pass
        await update.message.reply_text("❌ Ошибка при обработке файла. Убедитесь, что это текстовый файл.")
        return WAITING_FILE

def extract_configs(content: str) -> list:
    """Извлечение конфигов из файла с улучшенной логикой"""
    configs = []
    
    # Попробуем обработать как JSON
    try:
        data = json.loads(content)
        if isinstance(data, list):
            for item in data:
                if isinstance(item, str):
                    configs.append(item)
                else:
                    configs.append(json.dumps(item))
            return configs
        elif isinstance(data, dict) and 'configs' in data:
            for item in data['configs']:
                if isinstance(item, str):
                    configs.append(item)
                else:
                    configs.append(json.dumps(item))
            return configs
    except json.JSONDecodeError:
        pass  # Не JSON, продолжаем стандартную обработку
    
    # Стандартная обработка по строкам
    current_config = []
    for line in content.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        
        # Обнаружение начала нового конфига
        if any(stripped.startswith(proto) for proto in SUPPORTED_PROTOCOLS):
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
    
    return configs

async def handle_country(update: Update, context: CallbackContext):
    """Обработка выбора страны"""
    text = update.message.text.strip()
    user_id = update.message.from_user.id
    
    # Проверка, что текст является флагом
    if text in FLAG_COUNTRY_MAP:
        country_name = FLAG_COUNTRY_MAP[text]
        # Нормализуем название страны
        normalized_country = normalize_country_name(country_name)
        
        # Получаем коды страны
        country_codes = get_country_code(normalized_country)
        
        # Сохраняем данные о стране
        context.user_data['country'] = country_name
        context.user_data['target_country'] = normalized_country
        context.user_data['country_codes'] = country_codes
        
        logger.info(f"Пользователь {user_id} выбрал страну: {country_name} ({normalized_country})")
        
        # Предлагаем выбор режима поиска
        keyboard = [
            [InlineKeyboardButton("🔍 Быстрый поиск (по флагу)", callback_data='simple_search')],
            [InlineKeyboardButton("🔍 Строгий поиск (проверка IP)", callback_data='strict_search')],
            [InlineKeyboardButton("🔍 Комбинированный поиск", callback_data='combined_search')],
            [InlineKeyboardButton("🔙 Назад", callback_data='back_to_country')]
        ]
        reply_markup = InlineKeyboardMarkup(keyboard)
        
        await update.message.reply_text(
            f"🌍 Страна установлена: {country_name}\n"
            "Выберите режим поиска:\n"
            "• Быстрый: по ключевым словам и доменам\n"
            "• Строгий: проверка геолокации IP\n"
            "• Комбинированный: оба метода",
            reply_markup=reply_markup
        )
        return START
    else:
        await update.message.reply_text(
            "❌ Некорректный запрос. Пожалуйста, отправьте флаг страны.\n"
            "Примеры: 🇷🇺, 🇺🇸, 🇩🇪, 🇱🇻, 🇱🇹"
        )
        return WAITING_COUNTRY

async def simple_search(update: Update, context: CallbackContext):
    """Быстрый поиск конфигов по ключевым словам и доменам"""
    user_id = update.callback_query.from_user.id
    configs = context.user_data.get('configs', [])
    target_country = context.user_data.get('target_country', '')
    country_codes = context.user_data.get('country_codes', [])
    
    # Убедимся, что country_codes - это список
    if not isinstance(country_codes, list):
        country_codes = []
    
    logger.info(f"Начало быстрого поиска. Конфигов: {len(configs)}, Страна: {target_country}, Коды страны: {country_codes}")
    
    if not configs or not target_country:
        await context.bot.send_message(chat_id=user_id, text="❌ Ошибка: данные для поиска отсутствуют.")
        return ConversationHandler.END
    
    start_time = time.time()
    matched_configs = []
    progress_msg = await context.bot.send_message(chat_id=user_id, text="🔎 Начинаю быстрый поиск...")
    total_configs = len(configs)
    processed = 0
    context.user_data['simple_search_in_progress'] = True
    
    try:
        for i, config in enumerate(configs):
            if context.user_data.get('stop_simple_search'):
                break
            
            try:
                is_relevant = is_config_relevant(config, target_country, country_codes)
                if is_relevant:
                    matched_configs.append(config)
                    logger.debug(f"Конфиг #{i} соответствует стране {target_country}")
                else:
                    logger.debug(f"Конфиг #{i} не соответствует стране {target_country}")
            except Exception as e:
                logger.error(f"Ошибка проверки конфига #{i}: {e}", exc_info=True)
            
            processed += 1
            
            # Регулярное обновление прогресса
            if time.time() - context.user_data.get('progress_last_update', 0) > PROGRESS_UPDATE_INTERVAL or i == total_configs - 1:
                progress = min(processed / total_configs * 100, 100)
                progress_bar = create_progress_bar(progress)
                await context.bot.edit_message_text(
                    chat_id=user_id,
                    message_id=progress_msg.message_id,
                    text=f"🔎 Быстрый поиск: {progress_bar} {progress:.1f}%\n"
                         f"Обработано: {processed}/{total_configs}\n"
                         f"Найдено: {len(matched_configs)}"
                )
                context.user_data['progress_last_update'] = time.time()
            
            # Проверка необходимости остановки
            if context.user_data.get('stop_simple_search'):
                break
        
        logger.info(f"Найдено {len(matched_configs)} конфигов для {target_country}, обработка заняла {time.time()-start_time:.2f} сек")
        context.user_data['simple_search_in_progress'] = False
        
        if not matched_configs:
            await context.bot.edit_message_text(
                chat_id=user_id,
                message_id=progress_msg.message_id,
                text=f"❌ Конфигурации для {target_country} не найдены.")
            return ConversationHandler.END
        
        context.user_data['matched_configs'] = matched_configs
        
        # Обновляем сообщение с результатом
        await context.bot.edit_message_text(
            chat_id=user_id,
            message_id=progress_msg.message_id,
            text=f"✅ Найдено {len(matched_configs)} конфигов для {target_country}!"
        )
        
        await context.bot.send_message(
            chat_id=user_id,
            text=f"🌍 Для страны {target_country} найдено {len(matched_configs)} конфигов. Сколько конфигов прислать? (введите число от 1 до {len(matched_configs)})"
        )
        return WAITING_NUMBER
        
    except Exception as e:
        context.user_data['simple_search_in_progress'] = False
        logger.error(f"Ошибка быстрого поиска: {e}", exc_info=True)
        await context.bot.edit_message_text(
            chat_id=user_id,
            message_id=progress_msg.message_id,
            text="❌ Произошла ошибка при быстром поиске конфигураций."
        )
        return ConversationHandler.END

async def strict_search(update: Update, context: CallbackContext):
    """Строгий поиск конфигов с проверкой геолокации"""
    user_id = update.callback_query.from_user.id
    configs = context.user_data.get('configs', [])
    target_country = context.user_data.get('target_country', '')
    country_codes = [code.lower() for code in context.user_data.get('country_codes', [])]
    
    # Проверка доступности базы геолокации
    if geoip_db is None:
        logger.error("База геолокации не загружена, строгий поиск невозможен")
        await context.bot.send_message(
            chat_id=user_id,
            text="❌ База геолокации не загружена. Строгий поиск невозможен."
        )
        context.user_data['strict_in_progress'] = False
        return ConversationHandler.END
    
    if not configs or not target_country:
        await context.bot.send_message(chat_id=user_id, text="❌ Ошибка: данные для поиска отсутствуют.")
        return ConversationHandler.END
    
    start_time = time.time()
    valid_configs = []
    progress_msg = await context.bot.send_message(chat_id=user_id, text="🔎 Начинаю строгий поиск...")
    total_configs = len(configs)
    processed = 0
    context.user_data['strict_in_progress'] = True
    
    try:
        # Группировка конфигов по хостам
        host_to_configs = {}
        configs_without_host = []
        
        for config in configs:
            host = extract_host(config)
            if host:
                host = host.lower()  # Нормализуем хост к нижнему регистру
                if host not in host_to_configs:
                    host_to_configs[host] = []
                host_to_configs[host].append(config)
            else:
                # Сохраняем конфиги без хоста для ручной проверки
                configs_without_host.append(config)
        
        unique_hosts = list(host_to_configs.keys())
        total_hosts = len(unique_hosts)
        logger.info(f"Уникальных хостов: {total_hosts}, конфигов без хоста: {len(configs_without_host)}")
        
        # Проверка конфигов без IP по хешу и ключевым словам
        for config in configs_without_host:
            # Проверяем по ключевым словам
            if is_config_relevant(config, target_country, country_codes):
                logger.debug(f"Конфиг без IP релевантен по ключевым словам: {calculate_config_hash(config)}")
                valid_configs.append(config)
        
        if not unique_hosts:
            await context.bot.edit_message_text(
                chat_id=user_id,
                message_id=progress_msg.message_id,
                text=f"✅ Найдено {len(valid_configs)} конфигов без IP по ключевым словам."
            )
            context.user_data['matched_configs'] = valid_configs
            await context.bot.send_message(
                chat_id=user_id,
                text=f"🌍 Для страны {target_country} найдено {len(valid_configs)} валидных конфигов! Сколько конфигов прислать? (введите число от 1 до {len(valid_configs)})"
            )
            return WAITING_NUMBER
        
        # Создаем семафор для ограничения количества параллельных запросов
        semaphore = asyncio.Semaphore(MAX_CONCURRENT_DNS)
        
        # Функция для разрешения хоста с кэшированием
        async def resolve_host(host):
            # Используем нижний регистр для кэша
            host_lower = host.lower()
            # Проверка кэша
            if host_lower in dns_cache and (time.time() - dns_cache[host_lower]['timestamp']) < CACHE_TTL:
                return host, dns_cache[host_lower]['ip']
            
            async with semaphore:
                try:
                    resolver = dns.asyncresolver.Resolver()
                    resolver.timeout = DNS_TIMEOUT
                    resolver.lifetime = DNS_TIMEOUT
                    answer = await resolver.resolve(host, 'A')
                    if answer:
                        ip = answer[0].address
                        # Обновляем кэш в нижнем регистре
                        dns_cache[host_lower] = {'ip': ip, 'timestamp': time.time()}
                        # Удаляем старые записи, если кэш переполнен
                        if len(dns_cache) > CACHE_MAX_SIZE:
                            oldest = next(iter(dns_cache))
                            del dns_cache[oldest]
                        return host, ip
                except (dns.resolver.NoAnswer, dns.resolver.NXDOMAIN, 
                        dns.resolver.Timeout, dns.exception.DNSException) as e:
                    logger.debug(f"Не удалось разрешить {host}: {e}")
                except Exception as e:
                    logger.debug(f"Неизвестная ошибка при разрешении {host}: {e}")
            
            # Если не удалось разрешить, сохраняем в кэш как неудачу
            dns_cache[host_lower] = {'ip': None, 'timestamp': time.time()}
            return host, None
        
        # Разрешаем все хосты параллельно
        tasks = [resolve_host(host) for host in unique_hosts]
        results = await asyncio.gather(*tasks)
        host_ip_map = {host: ip for host, ip in results}
        
        # Проверяем геолокацию IP
        host_country_map = {}
        total_processed = 0
        
        resolved_ips = [ip for ip in host_ip_map.values() if ip]
        logger.info(f"Успешно разрешено IP: {len(resolved_ips)} из {total_hosts}")
        
        for host, ip in host_ip_map.items():
            if not ip:
                continue
                
            if context.user_data.get('stop_strict_search'):
                break
                
            # Проверка кэша геолокации
            if ip in geo_cache and (time.time() - geo_cache[ip]['timestamp']) < CACHE_TTL:
                host_country_map[host] = geo_cache[ip]['country']
                total_processed += 1
                continue
                
            try:
                async with geoip_db_lock:
                    if geoip_db:
                        try:
                            match = geoip_db.get(ip)
                            if match:
                                # Извлекаем код страны
                                country = match.get('country', {})
                                country_iso = country.get('iso_code', '').lower() if country else ''
                                
                                if country_iso:
                                    host_country_map[host] = country_iso
                                    
                                    # Обновляем кэш
                                    geo_cache[ip] = {'country': country_iso, 'timestamp': time.time()}
                                    # Удаляем старые записи, если кэш переполнен
                                    if len(geo_cache) > CACHE_MAX_SIZE:
                                        oldest = next(iter(geo_cache))
                                        del geo_cache[oldest]
                                else:
                                    logger.debug(f"Для IP {ip} не найден код страны")
                            else:
                                logger.debug(f"Для IP {ip} не найдена запись в базе геолокации")
                        except Exception as e:
                            logger.error(f"Ошибка геолокации для {host}: {e}")
                    else:
                        logger.error("База геолокации не загружена!")
            except Exception as e:
                logger.error(f"Ошибка при обработке геолокации: {e}")
            
            total_processed += 1
            
            # Обновление прогресса
            if time.time() - context.user_data.get('progress_last_update', 0) > PROGRESS_UPDATE_INTERVAL:
                progress = min(total_processed / total_hosts * 100, 100)
                progress_bar = create_progress_bar(progress)
                await context.bot.edit_message_text(
                    chat_id=user_id,
                    message_id=progress_msg.message_id,
                    text=f"🔎 Проверка геолокации: {progress_bar} {progress:.1f}%\n"
                         f"Обработано: {total_processed}/{total_hosts}"
                )
                context.user_data['progress_last_update'] = time.time()
        
        # Сбор валидных конфигов
        for host, country in host_country_map.items():
            if country in country_codes:
                valid_configs.extend(host_to_configs[host])
            else:
                logger.debug(f"Хост {host} (страна: {country}) не соответствует целевой стране {target_country} (коды: {country_codes})")
        
        logger.info(f"Коды страны для поиска: {country_codes}")
        logger.info(f"Найдено хостов с совпадением страны: {len(valid_configs)}")
        
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
            text=f"🌍 Для страны {target_country} найдено {len(valid_configs)} валидных конфигов! Сколько конфигов прислать? (введите число от 1 до {len(valid_configs)})"
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

async def combined_search(update: Update, context: CallbackContext):
    """Комбинированный поиск: быстрый + строгий"""
    user_id = update.callback_query.from_user.id
    configs = context.user_data.get('configs', [])
    target_country = context.user_data.get('target_country', '')
    country_codes = [code.lower() for code in context.user_data.get('country_codes', [])]
    
    if not configs or not target_country:
        await context.bot.send_message(chat_id=user_id, text="❌ Ошибка: данные для поиска отсутствуют.")
        return ConversationHandler.END
    
    start_time = time.time()
    progress_msg = await context.bot.send_message(chat_id=user_id, text="🔎 Начинаю комбинированный поиск...")
    context.user_data['strict_in_progress'] = True
    
    try:
        # Этап 1: Быстрый поиск
        prelim_configs = []
        total_configs = len(configs)
        processed = 0
        
        for i, config in enumerate(configs):
            if context.user_data.get('stop_strict_search'):
                break
                
            try:
                if is_config_relevant(config, target_country, country_codes):
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
                    text=f"🔎 Этап 1 (быстрый): {progress_bar} {progress:.1f}%\n"
                         f"Обработано: {processed}/{total_configs}\n"
                         f"Найдено: {len(prelim_configs)}"
                )
                context.user_data['progress_last_update'] = time.time()
        
        logger.info(f"Быстрый поиск: найдено {len(prelim_configs)} конфигов")
        
        if not prelim_configs:
            await context.bot.edit_message_text(
                chat_id=user_id,
                message_id=progress_msg.message_id,
                text=f"❌ Конфигурации для {target_country} не найдены."
            )
            return ConversationHandler.END
        
        # Этап 2: Строгая проверка геолокации
        await context.bot.edit_message_text(
            chat_id=user_id,
            message_id=progress_msg.message_id,
            text=f"🔎 Этап 2 (строгий): начинаю проверку {len(prelim_configs)} конфигов..."
        )
        
        # Временно сохраняем конфиги для строгой проверки
        original_configs = context.user_data['configs']
        context.user_data['configs'] = prelim_configs
        
        # Вызываем строгий поиск на отфильтрованном наборе
        result = await strict_search(update, context)
        
        # Восстанавливаем оригинальные конфиги
        context.user_data['configs'] = original_configs
        return result
        
    except Exception as e:
        logger.error(f"Ошибка комбинированного поиска: {e}", exc_info=True)
        context.user_data['strict_in_progress'] = False
        await context.bot.edit_message_text(
            chat_id=user_id,
            message_id=progress_msg.message_id,
            text="❌ Произошла ошибка при комбинированном поиске."
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
        context.user_data['stop_sending'] = False
        context.user_data['progress_last_update'] = time.time()
        
        await update.message.reply_text(f"⏫ Начинаю отправку {num} конфигов...")
        await send_configs(update, context)
        return ConversationHandler.END
        
    except ValueError:
        await update.message.reply_text("❌ Пожалуйста, введите число.")
        return WAITING_NUMBER
        
    except Exception as e:
        logger.error(f"Ошибка обработки количества конфигов: {e}")
        await update.message.reply_text("❌ Произошла ошибка при обработке запроса.")
        return WAITING_NUMBER

async def send_configs(update: Update, context: CallbackContext):
    """Отправка конфигов пользователю в формате кода с заголовком страны"""
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
    
    # Формируем заголовок в требуемом формате
    header = f"Конфиги для {country_name}:\n"
    full_text = header + "\n\n".join(matched_configs)
    
    # Разбиваем текст на части, не превышающие лимит Telegram
    messages = []
    while full_text:
        # Находим позицию для разбиения, чтобы не разрывать конфиг
        split_pos = min(MAX_MSG_LENGTH, len(full_text))
        if split_pos < len(full_text):
            # Ищем последний перенос строки перед split_pos
            split_pos = full_text.rfind('\n', 0, split_pos)
            if split_pos == -1:
                # Если переносов нет, разбиваем по максимальной длине
                split_pos = min(MAX_MSG_LENGTH, len(full_text))
        
        # Добавляем часть текста в сообщения
        part = full_text[:split_pos]
        messages.append(part)
        full_text = full_text[split_pos:]
    
    # Отправляем сообщения
    total_messages = len(messages)
    
    for i, message in enumerate(messages):
        if context.user_data.get('stop_sending'):
            break
            
        try:
            # Отправляем как код с форматированием
            await context.bot.send_message(
                chat_id=user_id,
                text=f"```\n{message}\n```",
                parse_mode="Markdown",
                disable_web_page_preview=True
            )
            
            # Обновляем прогресс
            if time.time() - context.user_data.get('progress_last_update', 0) > PROGRESS_UPDATE_INTERVAL:
                progress = min((i + 1) / total_messages * 100, 100)
                progress_bar = create_progress_bar(progress)
                await context.bot.send_message(
                    chat_id=user_id,
                    text=f"📤 Отправка: {progress_bar} {progress:.1f}%"
                )
                context.user_data['progress_last_update'] = time.time()
                
        except Exception as e:
            logger.error(f"Ошибка отправки сообщения: {e}")
            try:
                # Пытаемся отправить без форматирования, если возникла ошибка
                await context.bot.send_message(
                    chat_id=user_id,
                    text=message,
                    disable_web_page_preview=True
                )
            except Exception as e2:
                logger.error(f"Ошибка отправки текстового сообщения: {e2}")
    
    await context.bot.send_message(chat_id=user_id, text="✅ Все конфиги отправлены.")
    context.user_data['last_country'] = context.user_data['country']
    clear_temporary_data(context)
    return ConversationHandler.END

async def button_handler(update: Update, context: CallbackContext):
    """Обработка нажатий на кнопки"""
    query = update.callback_query
    await query.answer()
    
    # Проверка ограничения запросов для всех пользователей, кроме исключения
    if query.from_user.id != 1040929628 and not check_rate_limit(query.from_user.id, context):
        await query.edit_message_text("❌ Слишком много запросов. Пожалуйста, подождите минуту.")
        return ConversationHandler.END
    
    if query.data == 'add_file':
        await query.edit_message_text("📎 Пожалуйста, загрузите дополнительный файл с конфигурациями.")
        return WAITING_FILE
        
    elif query.data == 'set_country':
        await query.edit_message_text("🌍 Пожалуйста, отправьте флаг страны (например: 🇷🇺, 🇺🇸, 🇩🇪):")
        return WAITING_COUNTRY
        
    elif query.data == 'use_current_file':
        # Предлагаем выбрать страну
        await query.edit_message_text("🌍 Пожалуйста, отправьте флаг страны (например: 🇷🇺, 🇺🇸, 🇩🇪):")
        return WAITING_COUNTRY
        
    elif query.data == 'new_file':
        # Очищаем предыдущие данные
        clear_temporary_data(context)
        await query.edit_message_text("📎 Пожалуйста, загрузите новый файл с конфигурациями.")
        return WAITING_FILE
        
    elif query.data == 'cancel':
        await cancel(update, context)
        return ConversationHandler.END
        
    elif query.data == 'simple_search':
        await simple_search(update, context)
        return WAITING_NUMBER
        
    elif query.data == 'strict_search':
        await strict_search(update, context)
        return WAITING_NUMBER
        
    elif query.data == 'combined_search':
        await combined_search(update, context)
        return WAITING_NUMBER
        
    elif query.data == 'stop_sending':
        context.user_data['stop_sending'] = True
        await query.edit_message_text("⏹ Отправка конфигов остановлена.")
        return ConversationHandler.END
        
    elif query.data == 'stop_strict_search':
        context.user_data['stop_strict_search'] = True
        await query.edit_message_text("⏹ Строгий поиск остановлен.")
        return ConversationHandler.END
        
    elif query.data == 'stop_simple_search':
        context.user_data['stop_simple_search'] = True
        await query.edit_message_text("⏹ Простой поиск остановлен.")
        return ConversationHandler.END
        
    elif query.data == 'back_to_country':
        await query.edit_message_text("🌍 Пожалуйста, отправьте флаг страны (например: 🇷🇺, 🇺🇸, 🇩🇪):")
        return WAITING_COUNTRY
        
    return context.user_data.get('current_state', WAITING_COUNTRY)

async def cancel(update: Update, context: CallbackContext):
    """Отмена операции и очистка с улучшенной обработкой"""
    global geoip_file_path
    
    # Очистка временных данных пользователя
    clear_temporary_data(context)
    
    # Отмена поиска
    if 'strict_in_progress' in context.user_data:
        context.user_data['stop_strict_search'] = True
    if 'simple_search_in_progress' in context.user_data:
        context.user_data['stop_simple_search'] = True
    
    if update.callback_query:
        await update.callback_query.edit_message_text("❌ Операция отменена.")
    else:
        await update.message.reply_text("❌ Операция отменена.")
        
    return ConversationHandler.END

def check_rate_limit(user_id: int, context: CallbackContext) -> bool:
    """
    Проверка ограничения на количество запросов
    ИСКЛЮЧЕНИЕ: для пользователя с ID 1040929628 нет ограничений
    """
    # Пользователь с ID 1040929628 не имеет ограничений
    if user_id == 1040929628:
        return True
    
    # Реализация ограничения запросов
    current_time = time.time()
    
    # Получаем историю запросов из user_data
    request_history = context.user_data.get(f"rate_limit:{user_id}", [])
    
    # Удаляем старые записи
    request_history = [t for t in request_history if current_time - t < 60]
    
    # Проверяем лимит
    if len(request_history) >= 5:  # 5 запросов в минуту
        return False
    
    # Добавляем новый запрос
    request_history.append(current_time)
    context.user_data[f"rate_limit:{user_id}"] = request_history
    return True

def initialize_geoip_database_sync() -> bool:
    """Синхронная инициализация базы геолокации"""
    global geoip_file_path, geoip_db
    
    try:
        # Проверяем наличие кэшированной базы
        cache_dir = os.path.join(tempfile.gettempdir(), "geoip_cache")
        os.makedirs(cache_dir, exist_ok=True)
        
        # Генерируем URL для текущего месяца
        now = datetime.now(UTC)
        year_month = now.strftime("%Y-%m")
        cached_file = os.path.join(cache_dir, f"dbip-country-lite-{year_month}.mmdb")
        
        # Если файл уже есть в кэше, используем его
        if os.path.exists(cached_file):
            try:
                geoip_db = maxminddb.open_database(cached_file)
                geoip_file_path = cached_file
                logger.info(f"Используется кэшированная база геолокации: {cached_file}")
                return True
            except Exception as e:
                logger.error(f"Ошибка открытия кэшированной базы: {e}")
        
        # Скачиваем базу
        geoip_urls = [
            f"https://download.db-ip.com/free/dbip-country-lite-{year_month}.mmdb.gz",
            "https://github.com/P3TERX/GeoLite.mmdb/raw/download/GeoLite2-Country.mmdb",
            "https://cdn.jsdelivr.net/gh/Dreamacro/maxmind-geoip@release/Country.mmdb"
        ]
        
        for geoip_url in geoip_urls:
            try:
                logger.info(f"Скачивание базы геолокации: {geoip_url}")
                response = requests.get(geoip_url, timeout=30, stream=True)
                
                if response.status_code == 200:
                    content = b""
                    for chunk in response.iter_content(chunk_size=8192):
                        content += chunk
                    
                    # Распаковываем gzip если нужно
                    if geoip_url.endswith('.gz'):
                        with gzip.GzipFile(fileobj=io.BytesIO(content)) as gz_file:
                            db_content = gz_file.read()
                    else:
                        db_content = content
                    
                    # Сохраняем в кэш
                    with open(cached_file, 'wb') as f:
                        f.write(db_content)
                    
                    # Загружаем базу
                    geoip_db = maxminddb.open_database(cached_file)
                    geoip_file_path = cached_file
                    logger.info(f"База геолокации успешно загружена и сохранена в кэш: {cached_file}")
                    return True
            except Exception as e:
                logger.error(f"Ошибка загрузки базы {geoip_url}: {e}")
        
        # Если текущий месяц не доступен, пробуем предыдущий
        prev_month = (now.replace(day=1) - timedelta(days=1)).strftime("%Y-%m")
        cached_file_prev = os.path.join(cache_dir, f"dbip-country-lite-{prev_month}.mmdb")
        
        if os.path.exists(cached_file_prev):
            try:
                geoip_db = maxminddb.open_database(cached_file_prev)
                geoip_file_path = cached_file_prev
                logger.info(f"Используется кэшированная база за предыдущий месяц: {cached_file_prev}")
                return True
            except Exception as e:
                logger.error(f"Ошибка открытия кэшированной базы: {e}")
        
        logger.error("Не удалось загрузить базу геолокации ни из одного источника")
        return False
        
    except Exception as e:
        logger.error(f"Критическая ошибка инициализации базы геолокации: {e}", exc_info=True)
        geoip_db = None
        return False

async def initialize_geoip_database() -> bool:
    """Асинхронная инициализация базы геолокации"""
    loop = asyncio.get_running_loop()
    return await loop.run_in_executor(None, initialize_geoip_database_sync)

async def post_init(application: Application) -> None:
    """Асинхронная инициализация после запуска приложения"""
    try:
        logger.info("Инициализация базы геолокации...")
        success = await initialize_geoip_database()
        if not success:
            logger.error("Не удалось загрузить базу геолокации. Строгий поиск будет недоступен")
            # Пробуем альтернативный источник
            logger.info("Попытка использования локальной копии базы...")
            try:
                geoip_db = maxminddb.open_database('Country.mmdb')
                logger.info("Локальная копия базы геолокации успешно загружена")
            except:
                logger.error("Не удалось загрузить локальную копию базы")
        else:
            logger.info("База геолокации успешно загружена")
    except Exception as e:
        logger.error(f"Ошибка при инициализации базы геолокации: {e}", exc_info=True)

async def main() -> None:
    """Основная асинхронная функция запуска бота"""
    global app, loop
    
    # Получаем текущий event loop
    loop = asyncio.get_event_loop()
    
    # Создаем приложение
    application = (
        Application.builder()
        .token(TOKEN)
        .post_init(post_init)
        .build()
    )
    app = application
    
    # Устанавливаем вебхук
    if WEBHOOK_URL:
        logger.info(f"Установка вебхука: {WEBHOOK_URL}")
        await application.bot.set_webhook(WEBHOOK_URL)
    
    # Создаем обработчик диалога
    conv_handler = ConversationHandler(
        entry_points=[CommandHandler("check_configs", start_check)],
        states={
            START: [
                CallbackQueryHandler(button_handler)
            ],
            WAITING_FILE: [
                MessageHandler(filters.Document.TEXT, handle_file),
                CallbackQueryHandler(button_handler)
            ],
            WAITING_COUNTRY: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, handle_country),
                CallbackQueryHandler(button_handler)
            ],
            WAITING_NUMBER: [
                MessageHandler(filters.Regex(r'^\d+$'), handle_number),
                CallbackQueryHandler(button_handler)
            ]
        },
        fallbacks=[CommandHandler("cancel", cancel)],
        per_user=True,
        per_chat=True
    )
    
    application.add_handler(conv_handler)
    application.add_handler(CommandHandler("start", start_check))
    
    # Добавляем обработчик для команды /chek_configs (с опечаткой)
    application.add_handler(CommandHandler("chek_configs", force_start_check))
    
    # Инициализация и запуск приложения
    await application.initialize()
    await application.start()
    
    # Запускаем HTTP сервер в отдельном потоке
    server_thread = threading.Thread(target=run_http_server, daemon=True)
    server_thread.start()
    logger.info(f"HTTP сервер запущен в отдельном потоке на порту {PORT}")
    
    # Бесконечный цикл ожидания
    while True:
        await asyncio.sleep(3600)  # Спим 1 час

if __name__ == '__main__':
    asyncio.run(main())
