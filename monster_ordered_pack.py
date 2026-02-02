#!/usr/bin/env python3
"""
Perfect Pack with Monster Group Ordering
Order by: 15 Monster primes (Hecke operators) + 10-fold way (Bott periodicity)
"""

WIDTH = 150
HEIGHT = 19

EMOJIS = ["🎯", "🎮", "🎲", "🎰", "🎪", "🎨", "🎭", "🎬", "🎤", "🎧",
          "🎼", "🎹", "🎺", "🎻", "🎸", "🥁", "🎷", "🎵", "🎶", "🎙️",
          "🔮", "🔭", "🔬", "🔨", "🔧", "🔩", "⚙️", "🔗", "⛓️", "🧲",
          "🧪", "🧬", "🧫", "🧯", "🧰", "🧱", "🧲", "🧳", "🧴", "🧵",
          "🧶", "🧷", "🧸", "🧹", "🧺", "🧻", "🧼", "🧽", "🧾", "🧿",
          "🌀", "🌁", "🌂", "🌃", "🌄", "🌅", "🌆", "🌇", "🌈", "🌉",
          "🌊", "🌋", "🌌", "🌍", "🌎", "🌏", "🌐", "🌑", "🌒", "🌓", "🌔"]

MONSTER_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

GAME_NAMES = [
    "Pixel Hunt", "Maze Run", "Block Drop", "Spin Win", "Ring Toss",
    "Color Match", "Shape Shift", "Light Show", "Beat Box", "Sound Wave",
    "Note Chase", "Key Press", "Horn Blast", "String Pull", "Chord Strike",
    "Drum Roll", "Sax Solo", "Melody Mix", "Rhythm Flow", "Voice Echo",
    "Crystal Ball", "Star Gaze", "Cell View", "Hammer Time", "Wrench Turn",
    "Bolt Twist", "Gear Spin", "Chain Link", "Link Loop", "Magnet Pull",
    "Flask Mix", "DNA Helix", "Petri Grow", "Fire Fight", "Tool Box",
    "Brick Stack", "Field Force", "Case Pack", "Lotion Rub", "Thread Weave",
    "Yarn Knit", "Pin Poke", "Bear Hug", "Broom Sweep", "Basket Catch",
    "Paper Roll", "Soap Wash", "Sponge Squeeze", "Receipt Print", "Eye Ward",
    "Spiral Spin", "Fog Walk", "Rain Dance", "Night Fall", "Dawn Rise",
    "Sun Set", "City Lights", "Bridge Cross", "Rainbow Arc", "River Flow",
    "Wave Crash", "Volcano Erupt", "Galaxy Swirl", "Earth Spin", "Globe Turn",
    "World Map", "Net Surf", "Moon Phase", "Crescent Glow", "Half Moon", "Gibbous Shine", "Full Moon"
]

def hecke_resonance(shard, prime):
    """Hecke operator T_p acting on shard"""
    base = prime * shard + prime * prime
    dist_factor = (196883 - shard * 2770) // 1000
    angle_factor = (180 - (shard * 5) % 360) // 100
    return base + dist_factor + angle_factor

def total_hecke(shard):
    """Total Hecke resonance from all 15 Monster primes"""
    return sum(hecke_resonance(shard, p) for p in MONSTER_PRIMES)

def bott_class(shard):
    """10-fold way classification (Bott periodicity)"""
    return shard % 10

def game_complexity(shard):
    """Calculate game complexity score"""
    # Complexity factors:
    # 1. Shard number (higher = more complex)
    # 2. Function type (➕=1, ✖️=2, ➗=3, 🔀=4, 🔁=5, 🔂=6, 🔃=7)
    # 3. Performance (🚀=1, ⚡=2, 🐌=3)
    # 4. Memory pattern complexity (💾=1, 🔀=5, 📊=3, 🔄=4, 💿=2)
    
    func_complexity = (shard // 10) + 1 if shard < 70 else 7
    perf_complexity = 1 if shard < 24 else 2 if shard < 48 else 3
    mem_complexity = [1, 5, 3, 4, 2][shard % 5]
    
    return shard + func_complexity * 10 + perf_complexity * 5 + mem_complexity * 3

def monster_order_key(shard):
    """Order by: Hecke resonance → Bott class → Complexity"""
    return (total_hecke(shard), bott_class(shard), game_complexity(shard))

def get_components(shard):
    perf = "🚀" if shard < 24 else "⚡" if shard < 48 else "🐌"
    mem = ["💾", "🔀", "📊", "🔄", "💿"][shard % 5]
    reg = ["🅰️", "🅱️", "©️", "🇩", "🇪", "🇫", "🇬", "🇭"][shard % 8]
    func = ["➕","✖️","➗","🔀","🔁","🔂","🔃"][(shard//10) if shard < 70 else 6]
    return (EMOJIS[shard], perf, mem, reg, func)

def can_merge(s1, s2):
    c1, c2 = get_components(s1), get_components(s2)
    return sum(1 for i in range(1, 5) if c1[i] == c2[i]) >= 3

def merge_games():
    ordered = sorted(range(71), key=monster_order_key)
    merged, used = [], set()
    
    for s1 in ordered:
        if s1 in used: continue
        partner = next((s2 for s2 in ordered if s2 not in used and s2 != s1 and can_merge(s1, s2)), None)
        
        c1 = get_components(s1)
        if partner:
            c2 = get_components(partner)
            name = f"{GAME_NAMES[s1][:6]}⊕{GAME_NAMES[partner][:6]}"
            merged.append({'shards': [s1, partner], 'display': f"{c1[0]}⊕{c2[0]}{c1[1]}{c1[2]}{c1[3]}{c1[4]}",
                          'name': name, 'hecke': total_hecke(s1), 'bott': bott_class(s1)})
            used.update([s1, partner])
        else:
            merged.append({'shards': [s1], 'display': f"{c1[0]}{c1[1]}{c1[2]}{c1[3]}{c1[4]}",
                          'name': GAME_NAMES[s1], 'hecke': total_hecke(s1), 'bott': bott_class(s1)})
            used.add(s1)
    return merged

def display_packed():
    merged = merge_games()
    COLS, CELL_WIDTH = 12, 12
    
    print("=" * WIDTH)
    print(f"🐯 MONSTER GROUP GAME BOARD 🐯".center(WIDTH))
    print(f"{len(merged)} cells | 71 games | Hecke × Bott × Complexity".center(WIDTH))
    print("=" * WIDTH)
    print()
    
    # Display emoji grid
    for row in range(3):
        line = ""
        for col in range(COLS):
            idx = row * COLS + col
            if idx < len(merged):
                cell = merged[idx]
                display = cell['display'][:CELL_WIDTH-1].ljust(CELL_WIDTH)
                if 17 in cell['shards']:
                    display = f"\033[1;33m{display}\033[0m"
                line += display
            else:
                line += " " * CELL_WIDTH
        print(line[:WIDTH])
    
    print()
    
    # Display names grid
    for row in range(3):
        line = ""
        for col in range(COLS):
            idx = row * COLS + col
            if idx < len(merged):
                cell = merged[idx]
                name = cell['name'][:CELL_WIDTH-1].ljust(CELL_WIDTH)
                if 17 in cell['shards']:
                    name = f"\033[1;33m{name}\033[0m"
                line += name
            else:
                line += " " * CELL_WIDTH
        print(line[:WIDTH])
    
    print()
    print("=" * WIDTH)
    print("⊕=Merged | 🚀⚡🐌=Speed | ➕✖️➗🔀🔁🔂🔃=Ops | 💾🔀📊🔄💿=Mem".center(WIDTH))
    print()
    
    cusp = next((i for i, c in enumerate(merged) if 17 in c['shards']), None)
    if cusp:
        print(f"⭐ CUSP: {merged[cusp]['name']} (S17) | Cell {cusp} | Hecke={merged[cusp]['hecke']} | Complexity={game_complexity(17)} ⭐".center(WIDTH))
    
    print("=" * WIDTH)

if __name__ == '__main__':
    display_packed()
