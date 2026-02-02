#!/usr/bin/env python3
"""
zkERDFa-emoji Screen Projection
Calculate all 71 emoji hashes and project onto 150×38 terminal
"""

import sys

# Terminal dimensions
WIDTH = 150
HEIGHT = 38

# 71 unique emojis
EMOJIS = [
    "🎯", "🎮", "🎲", "🎰", "🎪", "🎨", "🎭", "🎬", "🎤", "🎧",
    "🎼", "🎹", "🎺", "🎻", "🎸", "🥁", "🎷", "🎵", "🎶", "🎙️",
    "🔮", "🔭", "🔬", "🔨", "🔧", "🔩", "⚙️", "🔗", "⛓️", "🧲",
    "🧪", "🧬", "🧫", "🧯", "🧰", "🧱", "🧲", "🧳", "🧴", "🧵",
    "🧶", "🧷", "🧸", "🧹", "🧺", "🧻", "🧼", "🧽", "🧾", "🧿",
    "🌀", "🌁", "🌂", "🌃", "🌄", "🌅", "🌆", "🌇", "🌈", "🌉",
    "🌊", "🌋", "🌌", "🌍", "🌎", "🌏", "🌐", "🌑", "🌒", "🌓",
    "🌔"
]

def calculate_emoji_hash(shard):
    """Calculate 8-emoji zkERDFa hash for shard"""
    emoji = EMOJIS[shard]
    
    # Performance
    perf = "🚀" if shard < 24 else "⚡" if shard < 48 else "🐌"
    
    # Memory pattern
    mem = ["💾", "🔀", "📊", "🔄", "💿"][shard % 5]
    
    # Register
    reg = ["🅰️", "🅱️", "©️", "🇩", "🇪", "🇫", "🇬", "🇭"][shard % 8]
    
    # Function type
    if shard < 10: func = "➕"
    elif shard < 20: func = "✖️"
    elif shard < 30: func = "➗"
    elif shard < 40: func = "🔀"
    elif shard < 50: func = "🔁"
    elif shard < 60: func = "🔂"
    else: func = "🔃"
    
    # Shard digits
    digits = "".join(["0️⃣","1️⃣","2️⃣","3️⃣","4️⃣","5️⃣","6️⃣","7️⃣","8️⃣","9️⃣"][int(d)] for d in str(shard))
    
    # Checksum
    checksum = ["✅","🔐","🔒","🔓","🔑","🗝️","🔏","🔎","🔍","🔬"][shard % 10]
    
    return emoji + perf + mem + reg + func + digits + checksum

def project_to_screen():
    """Project 71 games onto 150×38 terminal using optimal 6×12 grid"""
    
    # Optimal layout from MiniZinc: 6 cols × 12 rows
    COLS = 6
    ROWS = 12
    CELL_WIDTH = 25
    CELL_HEIGHT = 3
    
    # Calculate all hashes
    hashes = [calculate_emoji_hash(i) for i in range(71)]
    
    # Create screen buffer
    screen = [[' ' for _ in range(WIDTH)] for _ in range(HEIGHT)]
    
    # Project each game onto grid
    for shard in range(71):
        col = shard % COLS
        row = shard // COLS
        
        x = col * CELL_WIDTH
        y = row * CELL_HEIGHT
        
        # Skip if out of bounds
        if y + 2 >= HEIGHT or x + 20 >= WIDTH:
            continue
        
        # Line 1: Emoji hash
        hash_str = hashes[shard]
        for i, char in enumerate(hash_str[:20]):  # Truncate to fit
            if x + i < WIDTH:
                screen[y][x + i] = char
        
        # Line 2: Shard number
        shard_str = f"S{shard:02d}"
        if shard == 17:
            shard_str += "🐯"  # Cusp marker
        for i, char in enumerate(shard_str):
            if x + i < WIDTH:
                screen[y + 1][x + i] = char
    
    # Render screen
    for row in screen:
        print(''.join(row))

def main():
    # Header
    print("=" * WIDTH)
    print("zkERDFa-emoji Wall: 71 Arcade Games".center(WIDTH))
    print("Escaped-RDFa namespace | 6×12 grid | 150×38 terminal".center(WIDTH))
    print("=" * WIDTH)
    
    # Project games
    project_to_screen()
    
    # Footer
    print("=" * WIDTH)
    print(f"71 games | 8 emojis each | zkPerf + HE | Shard 17 = Cusp 🐯".center(WIDTH))
    print("=" * WIDTH)

if __name__ == '__main__':
    main()
