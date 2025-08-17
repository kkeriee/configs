# ... (предыдущий код до функции normalize_text) ...

def normalize_text(text: str) -> str:
    """Нормализация текста страны для поиска"""
    text = text.lower().strip()
    
    # Проверка кэша нормализации
    if text in country_normalization_cache:
        return country_normalization_cache[text]
    
    # Расширенный словарь перевода
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

async def handle_country(update: Update, context: CallbackContext):
    """Обработка ввода страны с улучшенной проверкой"""
    country_request = update.message.text
    context.user_data['country_request'] = country_request
    
    # Проверка на подозрительные запросы
    if len(country_request) > 50 or not re.match(r'^[\w\s\-.,]+$', country_request):
        await update.message.reply_text(
            "❌ Некорректный запрос. Пожалуйста, введите название страны.\n"
            "Примеры: 'США', 'Германия', 'Japan', 'UK'"
        )
        return WAITING_COUNTRY
    
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
        
        await update.message.reply_text(
            "❌ Страна не распознана. Пожалуйста, уточните название.\n"
            "Примеры: 'США', 'Германия', 'Japan', 'UK'"
        )
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

# ... (остальной код без изменений) ...
