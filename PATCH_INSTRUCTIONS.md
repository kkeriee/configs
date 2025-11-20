
PATCH INSTRUCTIONS — apply manually or with care

Summary of recommended changes to bot.py (file: bot.py):

1) Import the shared country data:
   Add near other imports:
       import country_data

2) After the file is parsed and `context.user_data['configs'] = configs` is assigned in
   async def handle_document(...):
   Insert code to automatically classify configs and send a paginated summary to the user:

    # Авто-классификация конфигов после загрузки — подсчёт по странам
    try:
        counts = {}
        flag_map = getattr(country_data, 'FLAG_COUNTRY_MAP', {})
        patterns = getattr(country_data, 'COUNTRY_PATTERNS', {})
        for cfg in configs:
            found = False
            for flag, cname in flag_map.items():
                if flag in cfg:
                    counts[cname] = counts.get(cname, 0) + 1
                    found = True
                    break
            if found:
                continue
            txt = cfg.lower()
            for cname, pats in patterns.items():
                for pat in pats:
                    try:
                        if re.search(pat, txt, flags=re.IGNORECASE):
                            counts[cname] = counts.get(cname, 0) + 1
                            found = True
                            break
                    except Exception:
                        if pat.lower() in txt:
                            counts[cname] = counts.get(cname, 0) + 1
                            found = True
                            break
                if found:
                    break
            if not found:
                counts['unknown'] = counts.get('unknown', 0) + 1
        # Отправляем сводку постранично
        MAX_LEN = globals().get('MAX_MSG_LENGTH', 3500)
        country_to_flags = {}
        for flag, cname in flag_map.items():
            country_to_flags.setdefault(cname, []).append(flag)
        lines = []
        for cname, cnt in sorted(counts.items(), key=lambda x:(-x[1], x[0])):
            if cname == 'unknown':
                lines.append(f"❓ Unknown - {cnt}")
            else:
                emoji = country_to_flags.get(cname, [''])[0] or ''
                lines.append(f"{emoji} - {cnt}")
        cur = ''
        for line in lines:
            if len(cur) + len(line) + 1 > MAX_LEN:
                await context.bot.send_message(chat_id=user.id, text=cur.rstrip())
                cur = line + '\\n'
            else:
                cur += line + '\\n'
        if cur:
            await context.bot.send_message(chat_id=user.id, text=cur.rstrip())
    except Exception as e:
        logger.error(f"Auto-classify failed: {e}")

   Important: keep indentation level consistent with handle_document's body.

3) In async def handle_flag_search(...):
   - after matching matched_configs, store the last_flag:
       context.user_data['last_flag'] = flag_emoji
   - reply with an inline keyboard button to repeat:
       keyboard = [[InlineKeyboardButton("🔁 Повторить поиск", callback_data='repeat_flag')]]
       reply_markup = InlineKeyboardMarkup(keyboard)
       await update.message.reply_text(f"✅ Найдено {len(matched_configs)} конфигов с флагом {flag_emoji}!", reply_markup=reply_markup)

4) In the inline buttons handler (button_handler), add handling for callback_data == 'repeat_flag':
    elif query.data == 'repeat_flag':
        last_flag = context.user_data.get('last_flag')
        configs = context.user_data.get('configs', [])
        if not last_flag or not configs:
            await query.edit_message_text("❌ Нет данных для повторного поиска.")
            return ConversationHandler.END
        matched_configs = [c for c in configs if last_flag in c]
        if not matched_configs:
            await query.edit_message_text(f"❌ Конфигурации, содержащие {last_flag}, не найдены при повторном поиске.")
            return ConversationHandler.END
        context.user_data['matched_configs'] = matched_configs
        context.user_data['country'] = f"конфиги с флагом {last_flag}"
        await query.edit_message_text(f"🔁 Повторный поиск: найдено {len(matched_configs)} конфигов с флагом {last_flag}. Сколько конфигов прислать? (введите число от 1 до {len(matched_configs)})")
        return WAITING_NUMBER

5) Tests & deploy:
   - After applying the changes, run flake/py_compile to verify syntax.
   - Test locally by running bot and sending a small configs file.
   - On Render.com, make sure the environment variables for TELEGRAM token and webhook are preserved.

Notes and recommendations:
 - Keep the country patterns dictionary (COUNTRY_PATTERNS) and FLAG_COUNTRY_MAP in a single shared module (country_data.py) and import it in bot.py. Avoid duplicating mappings.
 - For strict search improvements, consider:
     * preprocessing configs to extract hosts and IPs once (caching results)
     * using async concurrency for geoip lookups (already partly implemented)
     * robustly parsing different config formats (vmess/vless/ssr/ss/trojan)
 - For large files, consider background processing with job queue (Redis/RQ), but on Render free tier that's restricted — otherwise consider chunked processing with progress updates.
 - Keep messages within Telegram limits and paginate; current code uses MAX_MSG_LENGTH constant.

End of instructions.
