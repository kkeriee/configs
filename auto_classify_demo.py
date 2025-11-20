"""
auto_classify_demo.py

Demonstration script that shows how to classify configs by country using
country_data.py. This is a safe helper script (does not modify bot.py).
Run it with: python3 auto_classify_demo.py <path_to_configs_file>
"""

import sys
import os
import country_data
import re

def load_configs_from_file(path, max_configs=10000):
    configs = []
    current = []
    SUPPORTED_PROTOCOLS = ["vmess","vless","ss","ssr","trojan","socks5"]
    with open(path, 'r', encoding='utf-8', errors='replace') as f:
        for line in f:
            s = line.strip()
            if not s:
                continue
            if any(s.startswith(proto + "://") for proto in SUPPORTED_PROTOCOLS):
                if current:
                    configs.append("\\n".join(current))
                    current = []
            current.append(s)
    if current:
        configs.append("\\n".join(current))
    return configs

def classify(configs):
    flag_map = getattr(country_data, 'FLAG_COUNTRY_MAP', {})
    patterns = getattr(country_data, 'COUNTRY_PATTERNS', {})
    counts = {}
    for cfg in configs:
        matched = False
        for flag, cname in flag_map.items():
            if flag in cfg:
                counts[cname] = counts.get(cname, 0) + 1
                matched = True
                break
        if matched:
            continue
        txt = cfg.lower()
        for cname, pats in patterns.items():
            for pat in pats:
                try:
                    if re.search(pat, txt, flags=re.IGNORECASE):
                        counts[cname] = counts.get(cname, 0) + 1
                        matched = True
                        break
                except re.error:
                    if pat.lower() in txt:
                        counts[cname] = counts.get(cname, 0) + 1
                        matched = True
                        break
            if matched:
                break
        if not matched:
            counts['unknown'] = counts.get('unknown', 0) + 1
    return counts

def print_summary(counts):
    # invert flag_map
    flag_map = getattr(country_data, 'FLAG_COUNTRY_MAP', {})
    country_to_flags = {}
    for flag, cname in flag_map.items():
        country_to_flags.setdefault(cname, []).append(flag)
    items = sorted(counts.items(), key=lambda x:(-x[1], x[0]))
    for cname, cnt in items:
        emoji = country_to_flags.get(cname, [''])[0] if cname != 'unknown' else ''
        label = f"{emoji} - {cnt}" if cname != 'unknown' else f"❓ Unknown - {cnt}"
        print(label)

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python3 auto_classify_demo.py <configs_file.txt>")
        sys.exit(1)
    path = sys.argv[1]
    if not os.path.exists(path):
        print("File not found:", path)
        sys.exit(1)
    cfgs = load_configs_from_file(path)
    print(f"Loaded {len(cfgs)} configs from {path}")
    counts = classify(cfgs)
    print_summary(counts)
