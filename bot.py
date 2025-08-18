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
    CallbackContext
)
import maxminddb
import dns.asyncresolver
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
DNS_TIMEOUT = 8.0  # Таймаут для DNS-запросов (секунды)
CACHE_MAX_SIZE = 5000  # Максимальный размер кэшей
CACHE_TTL = 3600  # Время жизни кэша в секундах

# Состояния разговора
START, WAITING_FILE, WAITING_COUNTRY, WAITING_NUMBER = range(4)

# Поддерживаемые протоколы
SUPPORTED_PROTOCOLS = ['vmess', 'vless', 'trojan', 'ss', 'ssr', 'socks', 'http', 'https']

def clear_temporary_data(context: CallbackContext):
    """Очистка временных данных в user_data"""
    keys_to_clear = [
        'matched_configs', 'current_index', 'stop_sending',
        'strict_in_progress', 'stop_strict_search', 'progress_message_id',
        'progress_last_update', 'stop_simple_search', 'simple_search_in_progress'
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
    
    ОСНОВНОЕ ИСПРАВЛЕНИЕ: улучшена обработка названий стран для соответствия
    формату, используемому в COUNTRY_PATTERNS
    """
    config_lower = config.lower()
    
    # Убедимся, что country_codes - это список
    if not isinstance(country_codes, list):
        country_codes = []
    
    # Проверяем по домену
    domain = extract_domain(config)
    if domain:
        tld = domain.split('.')[-1].lower()
        if tld in country_codes:
            return True
    
    # Проверяем по ключевым словам с нормализацией целевой страны
    return detect_by_keywords(config_lower, target_country)

def detect_by_keywords(config_lower: str, target_country: str) -> bool:
    """
    Обнаружение страны по ключевым словам
    
    ОСНОВНОЕ ИСПРАВЛЕНИЕ: добавлена нормализация названия страны для
    корректного поиска в COUNTRY_PATTERNS
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
        
        # VLESS
        if config.startswith('vless://'):
            try:
                # Извлечение хоста из URL
                url = config.split('://')[1].split('?')[0]
                host = url.split('@')[1].split(':')[0]
                return host
            except Exception as e:
                logger.debug(f"Ошибка обработки VLESS: {e}")
        
        # Trojan
        if config.startswith('trojan://'):
            try:
                # Извлечение хоста из URL
                url = config.split('://')[1].split('?')[0]
                host = url.split('@')[1].split(':')[0]
                return host
            except Exception as e:
                logger.debug(f"Ошибка обработки Trojan: {e}")
        
        # Общий случай
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

async def generate_country_instructions(country: str) -> str:
    """Генерация инструкций для страны"""
    return COUNTRY_INSTRUCTIONS.get(country.lower(), f"Инструкция по настройке для {country}")

async def start_check(update: Update, context: CallbackContext):
    """Начало проверки конфигов с выбором действия"""
    # Проверка ограничения запросов для всех пользователей, кроме исключения
    if update.message.from_user.id != 1040929628 and not check_rate_limit(update.message.from_user.id):
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
            f"Последняя страна: {context.user_data['last_country']}\n\n"
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
        configs = []
        current_config = []
        max_lines = 10000  # Максимальное количество строк на конфиг
        line_count = 0
        
        for line in content.splitlines():
            line_count += 1
            if line_count > max_lines:
                break
                
            stripped = line.strip()
            if stripped:
                # Проверка на начало нового конфига
                if any(stripped.startswith(proto + "://") for proto in SUPPORTED_PROTOCOLS):
                    if current_config:
                        configs.append("".join(current_config))
                        current_config = []
                    # Проверка лимита
                    if len(configs) >= MAX_CONFIGS:
                        break
                current_config.append(stripped)
        
        # Добавляем последний конфиг
        if current_config and len(configs) < MAX_CONFIGS:
            configs.append("".join(current_config))
        
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
        return START
    except Exception as e:
        logger.error(f"Ошибка обработки файла: {e}", exc_info=True)
        os.unlink(file_path)
        await update.message.reply_text("❌ Ошибка при обработке файла. Убедитесь, что это текстовый файл.")
        return WAITING_FILE

async def handle_country(update: Update, context: CallbackContext):
    """Обработка выбора страны"""
    text = update.message.text.strip()
    user_id = update.message.from_user.id
    
    # Проверка, что текст является флагом
    if text in FLAG_COUNTRY_MAP:
        country_name = FLAG_COUNTRY_MAP[text]
        # Нормализуем название страны
        normalized_country = normalize_country_name(country_name)
        
        # Сохраняем данные о стране
        context.user_data['country'] = country_name
        context.user_data['target_country'] = normalized_country
        context.user_data['country_codes'] = get_country_code(normalized_country)
        
        logger.info(f"Пользователь {user_id} выбрал страну: {country_name} ({normalized_country})")
        
        # Предлагаем выбор режима поиска
        keyboard = [
            [InlineKeyboardButton("🔍 Простой поиск (быстрый)", callback_data='simple_search')],
            [InlineKeyboardButton("🔍 Строгий поиск (точный)", callback_data='strict_search')],
            [InlineKeyboardButton("🔙 Назад", callback_data='back_to_country')]
        ]
        reply_markup = InlineKeyboardMarkup(keyboard)
        await update.message.reply_text(
            f"🌍 Страна установлена: {country_name}\n\n"
            "Выберите режим поиска:",
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
    """Простой поиск конфигов только по ключевым словам и доменам"""
    user_id = update.callback_query.from_user.id if update.callback_query else update.message.from_user.id
    configs = context.user_data.get('configs', [])
    target_country = context.user_data.get('target_country', '')
    country_codes = context.user_data.get('country_codes', [])
    
    # Убедимся, что country_codes - это список
    if not isinstance(country_codes, list):
        country_codes = []
    
    logger.info(f"Начало простого поиска. Конфигов: {len(configs)}, Страна: {target_country}, Коды страны: {country_codes}")
    
    if not configs or not target_country:
        await context.bot.send_message(chat_id=user_id, text="❌ Ошибка: данные для поиска отсутствуют.")
        return ConversationHandler.END

    start_time = time.time()
    matched_configs = []
    progress_msg = await context.bot.send_message(chat_id=user_id, text="🔎 Начинаю простой поиск...")
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
                    text=f"🔎 Простой поиск: {progress_bar} {progress:.1f}%\n"
                         f"Обработано: {processed}/{total_configs}")
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
            text=f"✅ Найдено {len(matched_configs)} конфигов для {target_country}!")
        
        await context.bot.send_message(
            chat_id=user_id,
            text=f"🌍 Для страны {target_country} найдено {len(matched_configs)} конфигов. Сколько конфигов прислать? (введите число от 1 до {len(matched_configs)})")
        
        return WAITING_NUMBER
    except Exception as e:
        context.user_data['simple_search_in_progress'] = False
        logger.error(f"Ошибка простого поиска: {e}", exc_info=True)
        await context.bot.edit_message_text(
            chat_id=user_id,
            message_id=progress_msg.message_id,
            text="❌ Произошла ошибка при простом поиске конфигураций.")
        return ConversationHandler.END

async def strict_search(update: Update, context: CallbackContext):
    """Строгий поиск конфигов с проверкой геолокации"""
    user_id = update.callback_query.from_user.id if update.callback_query else update.message.from_user.id
    configs = context.user_data.get('configs', [])
    target_country = context.user_data.get('target_country', '')
    
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
        # Этап 1: Предварительный отбор по ключевым словам
        prelim_configs = []
        for i, config in enumerate(configs):
            if context.user_data.get('stop_strict_search'):
                break
            try:
                if is_config_relevant(config, target_country, context.user_data['country_codes']):
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
                    text=f"🔎 Этап 1: {progress_bar} {progress:.1f}%\n"
                         f"Обработано: {processed}/{total_configs}")
                context.user_data['progress_last_update'] = time.time()
            # Проверка необходимости остановки
            if context.user_data.get('stop_strict_search'):
                break
        
        logger.info(f"Предварительно найдено {len(prelim_configs)} конфигов, обработка заняла {time.time()-start_time:.2f} сек")
        
        if not prelim_configs:
            await context.bot.edit_message_text(
                chat_id=user_id,
                message_id=progress_msg.message_id,
                text=f"❌ Конфигурации для {target_country} не найдены.")
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
                text=f"❌ Не найдено хостов для проверки геолокации.")
            return ConversationHandler.END
        
        # Этап 2: Проверка геолокации для уникальных хостов
        host_country_map = {}
        total_processed = 0
        stop_search = False
        
        for host in unique_hosts:
            if context.user_data.get('stop_strict_search'):
                stop_search = True
                break
            
            try:
                # Получаем IP-адрес хоста
                ip = socket.gethostbyname(host)
                # Проверяем геолокацию
                with geoip_db_lock:
                    if geoip_db:
                        try:
                            match = geoip_db.get(ip)
                            if match and 'country' in match:
                                country_iso = match['country']['iso_code'].lower()
                                host_country_map[host] = country_iso
                        except Exception as e:
                            logger.debug(f"Ошибка геолокации для {host}: {e}")
            except Exception as e:
                logger.debug(f"Не удалось разрешить {host}: {e}")
            
            total_processed += 1
            # Обновление прогресса
            if time.time() - context.user_data.get('progress_last_update', 0) > PROGRESS_UPDATE_INTERVAL:
                progress = min(total_processed / total_hosts * 100, 100)
                progress_bar = create_progress_bar(progress)
                await context.bot.edit_message_text(
                    chat_id=user_id,
                    message_id=progress_msg.message_id,
                    text=f"🔎 Этап 2: {progress_bar} {progress:.1f}%\n"
                         f"Обработано: {total_processed}/{total_hosts}")
                context.user_data['progress_last_update'] = time.time()
            
            # Проверка необходимости остановки
            if context.user_data.get('stop_strict_search'):
                stop_search = True
                break
        
        # Сбор валидных конфигов
        for host in unique_hosts:
            if context.user_data.get('stop_strict_search'):
                break
            country = host_country_map.get(host)
            if country and country.lower() == target_country.split()[-1].lower():
                valid_configs.extend(host_to_configs[host])
        
        total_time = time.time() - start_time
        context.user_data['strict_in_progress'] = False
        
        # Отправляем результат
        if context.user_data.get('stop_strict_search'):
            await context.bot.edit_message_text(
                chat_id=user_id,
                message_id=progress_msg.message_id,
                text=f"⏹ Строгий поиск остановлен. Найдено {len(valid_configs)} конфигов.")
        else:
            await context.bot.edit_message_text(
                chat_id=user_id,
                message_id=progress_msg.message_id,
                text=f"✅ Строгий поиск завершен за {total_time:.2f} сек. Найдено {len(valid_configs)} конфигов.")
        
        if not valid_configs:
            await context.bot.send_message(chat_id=user_id, text="❌ Конфигурации не найдены.")
            return ConversationHandler.END
        
        context.user_data['matched_configs'] = valid_configs
        await context.bot.send_message(
            chat_id=user_id,
            text=f"🌍 Для страны {target_country} найдено {len(valid_configs)} валидных конфигов! Сколько конфигов прислать? (введите число от 1 до {len(valid_configs)})")
        return WAITING_NUMBER
    except Exception as e:
        logger.error(f"Ошибка строгого поиска: {e}", exc_info=True)
        context.user_data['strict_in_progress'] = False
        await context.bot.edit_message_text(
            chat_id=user_id,
            message_id=progress_msg.message_id,
            text="❌ Произошла ошибка при строгом поиске конфигураций.")
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
    header = f"Конфиги для {country_name}:"
    messages = []
    current_message = header
    
    for config in matched_configs:
        config_line = f"{config}\n"
        # Проверяем, не превысит ли добавление этой строки лимит
        if len(current_message) + len(config_line) > MAX_MSG_LENGTH:
            messages.append(current_message)
            current_message = header + config_line  # Начинаем новое сообщение с заголовка
        
        # Если даже одна строка конфига слишком длинная
        if len(config_line) > MAX_MSG_LENGTH:
            # Разбиваем длинный конфиг на части
            for i in range(0, len(config_line), MAX_MSG_LENGTH - len(header) - 1):
                part = config_line[i:i + MAX_MSG_LENGTH - len(header) - 1]
                messages.append(header + part)
        else:
            current_message += config_line
    
    # Добавляем последнее сообщение
    if len(current_message) > len(header):
        messages.append(current_message)
    
    # Отправляем сообщения
    for i, message in enumerate(messages):
        if context.user_data.get('stop_sending'):
            break
        
        try:
            await context.bot.send_message(
                chat_id=user_id,
                text=message,
                disable_web_page_preview=True
            )
            # Обновляем прогресс
            if time.time() - context.user_data.get('progress_last_update', 0) > PROGRESS_UPDATE_INTERVAL:
                progress = min((i + 1) / len(messages) * 100, 100)
                progress_bar = create_progress_bar(progress)
                await context.bot.send_message(
                    chat_id=user_id,
                    text=f"📤 Отправка: {progress_bar} {progress:.1f}%"
                )
                context.user_data['progress_last_update'] = time.time()
        except Exception as e:
            logger.error(f"Ошибка отправки сообщения: {e}")
            try:
                await context.bot.send_message(
                    chat_id=user_id,
                    text=f"⚠️ Ошибка отправки части {i+1}. Продолжаю..."
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
    if query.from_user.id != 1040929628 and not check_rate_limit(query.from_user.id):
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
    
    await update.callback_query.edit_message_text("❌ Операция отменена.") if update.callback_query else await update.message.reply_text("❌ Операция отменена.")
    return ConversationHandler.END

def check_rate_limit(user_id: int) -> bool:
    """
    Проверка ограничения на количество запросов
    
    ИСКЛЮЧЕНИЕ: для пользователя с ID 1040929628 нет ограничений
    """
    # Пользователь с ID 1040929628 не имеет ограничений
    if user_id == 1040929628:
        return True
    
    # Реализация ограничения запросов
    current_time = time.time()
    user_key = f"rate_limit:{user_id}"
    
    # Получаем историю запросов из user_data
    request_history = context.user_data.get(user_key, [])
    
    # Удаляем старые записи
    request_history = [t for t in request_history if current_time - t < 60]
    
    # Проверяем лимит
    if len(request_history) >= 5:  # 5 запросов в минуту
        return False
    
    # Добавляем новый запрос
    request_history.append(current_time)
    context.user_data[user_key] = request_history
    
    return True

def post_init(application: Application) -> None:
    """Инициализация после запуска приложения с улучшенной обработкой ошибок"""
    try:
        logger.info("Инициализация базы геолокации...")
        if not initialize_geoip_database_sync():
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
    
    # Запуск бота
    logger.info("Запуск бота...")
    application.run_polling()

if __name__ == '__main__':
    main()
