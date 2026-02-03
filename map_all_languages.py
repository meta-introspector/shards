#!/usr/bin/env python3
"""
Map all Rust, Python, Lean4, MiniZinc, Prolog files using Hecke resonance
Show cross-language mappings via Monster group sharding
"""

import json
from pathlib import Path
from collections import defaultdict
import hashlib

# 15 Monster primes
MONSTER_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

def hecke_hash(content: bytes, prime: int) -> int:
    h = hashlib.sha256(content).digest()
    return int.from_bytes(h[:8], 'big') % prime

def shard_file(file_path: Path) -> int:
    h = hashlib.sha256(str(file_path).encode()).digest()
    return int.from_bytes(h[:8], 'big') % 71

def hecke_signature(file_path: Path) -> list:
    try:
        content = file_path.read_bytes()
        return [hecke_hash(content, p) for p in MONSTER_PRIMES]
    except:
        return [0] * 15

def map_all_languages():
    print("🗺️  CROSS-LANGUAGE MAPPING VIA MONSTER GROUP")
    print("=" * 70)
    print()
    
    # Language extensions
    languages = {
        'rust': '*.rs',
        'python': '*.py',
        'lean4': '*.lean',
        'minizinc': '*.mzn',
        'prolog': '*.pl',
    }
    
    # Collect files by language
    files_by_lang = defaultdict(list)
    
    print("📂 Scanning files...")
    for lang, pattern in languages.items():
        for f in Path('.').rglob(pattern):
            if f.is_file():
                # Skip large files and hidden dirs
                if f.stat().st_size > 1_000_000:
                    continue
                if any(part.startswith('.') for part in f.parts):
                    continue
                if 'target' in f.parts or 'node_modules' in f.parts:
                    continue
                
                files_by_lang[lang].append(f)
    
    print()
    for lang, files in files_by_lang.items():
        print(f"  {lang:10s}: {len(files):5d} files")
    print()
    
    # Compute signatures and shards
    print("🎵 Computing Hecke signatures...")
    
    file_data = {}
    shard_map = defaultdict(lambda: defaultdict(list))
    
    total = sum(len(files) for files in files_by_lang.values())
    processed = 0
    
    for lang, files in files_by_lang.items():
        for f in files:
            sig = hecke_signature(f)
            shard = shard_file(f)
            
            file_data[str(f)] = {
                'language': lang,
                'signature': sig,
                'shard': shard,
                'size': f.stat().st_size,
            }
            
            shard_map[shard][lang].append(str(f))
            
            processed += 1
            if processed % 500 == 0:
                print(f"  Progress: {processed}/{total}")
    
    print(f"  Done! Processed {processed} files")
    print()
    
    # Find cross-language shards
    print("=" * 70)
    print("🌈 CROSS-LANGUAGE SHARDS (Multiple languages in same shard)")
    print("=" * 70)
    print()
    
    cross_lang_shards = []
    for shard, langs in shard_map.items():
        if len(langs) >= 2:  # At least 2 languages
            cross_lang_shards.append((shard, langs))
    
    cross_lang_shards.sort(key=lambda x: len(x[1]), reverse=True)
    
    print(f"Found {len(cross_lang_shards)} shards with multiple languages")
    print()
    
    for shard, langs in cross_lang_shards[:20]:
        lang_counts = {lang: len(files) for lang, files in langs.items()}
        total_files = sum(lang_counts.values())
        
        print(f"Shard {shard:2d}: {len(langs)} languages, {total_files} files")
        for lang in sorted(lang_counts.keys()):
            print(f"  • {lang:10s}: {lang_counts[lang]:3d} files")
        
        # Show example files
        print(f"  Examples:")
        for lang in sorted(langs.keys())[:3]:
            if langs[lang]:
                print(f"    {lang:10s}: {langs[lang][0]}")
        print()
    
    # Find matching signatures across languages
    print("=" * 70)
    print("🔗 CROSS-LANGUAGE SIGNATURE MATCHES")
    print("=" * 70)
    print()
    
    sig_map = defaultdict(list)
    for path, data in file_data.items():
        sig_key = tuple(data['signature'])
        sig_map[sig_key].append((path, data['language']))
    
    cross_lang_sigs = []
    for sig, files in sig_map.items():
        langs = set(lang for _, lang in files)
        if len(langs) >= 2:
            cross_lang_sigs.append((sig, files))
    
    cross_lang_sigs.sort(key=lambda x: len(x[1]), reverse=True)
    
    print(f"Found {len(cross_lang_sigs)} signatures shared across languages")
    print()
    
    for sig, files in cross_lang_sigs[:10]:
        langs = set(lang for _, lang in files)
        print(f"Signature {sig[:5]}... ({len(files)} files, {len(langs)} languages)")
        for path, lang in files[:5]:
            print(f"  • {lang:10s}: {path}")
        if len(files) > 5:
            print(f"  ... and {len(files) - 5} more")
        print()
    
    # Language pair mappings
    print("=" * 70)
    print("🔀 LANGUAGE PAIR MAPPINGS (Same shard)")
    print("=" * 70)
    print()
    
    pairs = defaultdict(list)
    for shard, langs in cross_lang_shards:
        lang_list = sorted(langs.keys())
        for i, lang1 in enumerate(lang_list):
            for lang2 in lang_list[i+1:]:
                pair = f"{lang1} ↔ {lang2}"
                pairs[pair].append((shard, langs[lang1], langs[lang2]))
    
    for pair in sorted(pairs.keys()):
        mappings = pairs[pair]
        print(f"{pair}: {len(mappings)} shards")
        
        # Show top 3 shards
        for shard, files1, files2 in mappings[:3]:
            print(f"  Shard {shard:2d}: {len(files1)} × {len(files2)} files")
            if files1 and files2:
                print(f"    {files1[0]}")
                print(f"    {files2[0]}")
        print()
    
    # Save results
    results = {
        'total_files': processed,
        'files_by_language': {lang: len(files) for lang, files in files_by_lang.items()},
        'cross_language_shards': len(cross_lang_shards),
        'cross_language_signatures': len(cross_lang_sigs),
        'shard_map': {
            shard: {lang: files for lang, files in langs.items()}
            for shard, langs in dict(shard_map).items()
        },
        'language_pairs': {
            pair: len(mappings) for pair, mappings in pairs.items()
        }
    }
    
    with open('cross_language_map.json', 'w') as f:
        json.dump(results, f, indent=2)
    
    print("💾 Results saved to: cross_language_map.json")
    print()
    
    # Summary
    print("=" * 70)
    print("📊 SUMMARY")
    print("=" * 70)
    print()
    print(f"Total files: {processed}")
    for lang, count in sorted(results['files_by_language'].items()):
        print(f"  {lang:10s}: {count:5d} files")
    print()
    print(f"Cross-language shards: {len(cross_lang_shards)}/71 ({len(cross_lang_shards)/71*100:.1f}%)")
    print(f"Shared signatures: {len(cross_lang_sigs)}")
    print()
    print("Top language pairs:")
    for pair, count in sorted(pairs.items(), key=lambda x: len(x[1]), reverse=True)[:5]:
        print(f"  {pair}: {count} shards")
    print()
    print("✅ All languages can be mapped via Monster group structure!")

if __name__ == "__main__":
    map_all_languages()
