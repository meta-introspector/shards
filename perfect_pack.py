#!/usr/bin/env python3
"""
Perfect Pack with Game Merging
Merge games sharing 3+ emoji components, display with ⊕ symbol
Optimal: 36 merged cells in 12×3 grid for 150×19 terminal
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

def get_components(shard):
    """Get emoji components for a shard"""
    perf = "🚀" if shard < 24 else "⚡" if shard < 48 else "🐌"
    mem = ["💾", "🔀", "📊", "🔄", "💿"][shard % 5]
    reg = ["🅰️", "🅱️", "©️", "🇩", "🇪", "🇫", "🇬", "🇭"][shard % 8]
    
    if shard < 10: func = "➕"
    elif shard < 20: func = "✖️"
    elif shard < 30: func = "➗"
    elif shard < 40: func = "🔀"
    elif shard < 50: func = "🔁"
    elif shard < 60: func = "🔂"
    else: func = "🔃"
    
    return (EMOJIS[shard], perf, mem, reg, func)

def can_merge(s1, s2):
    """Check if two shards can merge (share 3+ components)"""
    c1 = get_components(s1)
    c2 = get_components(s2)
    shared = sum(1 for i in range(1, 5) if c1[i] == c2[i])  # Skip game emoji
    return shared >= 3

def merge_games():
    """Merge 71 games into ~36 cells"""
    merged = []
    used = set()
    
    for s1 in range(71):
        if s1 in used:
            continue
        
        # Try to find merge partner
        partner = None
        for s2 in range(s1 + 1, 71):
            if s2 not in used and can_merge(s1, s2):
                partner = s2
                break
        
        if partner:
            # Merge s1 + partner
            c1 = get_components(s1)
            c2 = get_components(partner)
            merged.append({
                'shards': [s1, partner],
                'display': f"{c1[0]}⊕{c2[0]}{c1[1]}{c1[2]}{c1[3]}{c1[4]}"
            })
            used.add(s1)
            used.add(partner)
        else:
            # No merge partner, standalone
            c = get_components(s1)
            merged.append({
                'shards': [s1],
                'display': f"{c[0]}{c[1]}{c[2]}{c[3]}{c[4]}"
            })
            used.add(s1)
    
    return merged

def display_packed():
    """Display perfectly packed emoji wall"""
    merged = merge_games()
    
    # Optimal layout from MiniZinc: 12 cols × 3 rows
    COLS = 12
    CELL_WIDTH = 12
    
    print("=" * WIDTH)
    print(f"zkERDFa Perfect Pack: {len(merged)} cells (71 games, {71-len(merged)} merged)".center(WIDTH))
    print("=" * WIDTH)
    
    for row in range(3):
        line = ""
        for col in range(COLS):
            idx = row * COLS + col
            if idx < len(merged):
                cell = merged[idx]
                display = cell['display'][:CELL_WIDTH-1]  # Truncate to fit
                shards_str = "+".join(str(s) for s in cell['shards'])
                
                # Pad to cell width
                line += display.ljust(CELL_WIDTH)
            else:
                line += " " * CELL_WIDTH
        print(line[:WIDTH])  # Ensure doesn't exceed width
    
    print("=" * WIDTH)
    print(f"⊕ = Merge symbol | Cusp at S17 | {len(merged)}/{71} cells used".center(WIDTH))

if __name__ == '__main__':
    display_packed()
