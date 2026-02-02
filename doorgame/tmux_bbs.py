#!/usr/bin/env python3
"""TradeWars BBS for tmux - 141x40"""

import sys
import time
import random

WIDTH = 141
HEIGHT = 40

# ANSI colors
RESET = "\033[0m"
BOLD = "\033[1m"
CYAN = "\033[36m"
GREEN = "\033[32m"
YELLOW = "\033[33m"
MAGENTA = "\033[35m"
RED = "\033[31m"

def clear():
    print("\033[2J\033[H", end="")
    sys.stdout.flush()

def draw_box(x, y, w, h, title=""):
    """Draw box at position"""
    # Top
    print(f"\033[{y};{x}H╔{'═' * (w-2)}╗", end="")
    if title:
        title_x = x + (w - len(title)) // 2
        print(f"\033[{y};{title_x}H{title}", end="")
    
    # Sides
    for i in range(1, h-1):
        print(f"\033[{y+i};{x}H║{' ' * (w-2)}║", end="")
    
    # Bottom
    print(f"\033[{y+h-1};{x}H╚{'═' * (w-2)}╝", end="")

def center_text(y, text, color=GREEN):
    x = (WIDTH - len(text)) // 2
    print(f"\033[{y};{x}H{color}{text}{RESET}", end="")

def draw_bbs():
    clear()
    
    # Header
    draw_box(1, 1, WIDTH, 5, f"{BOLD}{CYAN}🔮⚡ TRADEWARS P2P BBS 📻🦞{RESET}")
    center_text(3, f"tmux: {WIDTH}x{HEIGHT} | Shards: 71 | Peers: 4", CYAN)
    
    # Main content area
    draw_box(1, 6, WIDTH, HEIGHT-12)
    
    # Player scores
    print(f"\033[7;3H{BOLD}{GREEN}PLAYER SCORES{RESET}")
    print(f"\033[8;3H{'─' * (WIDTH-4)}", end="")
    
    players = [
        {"rank": 1, "id": "peer-boat-01", "turn": 5, "lobsters": 12, "score": 8520, "status": "🟢"},
        {"rank": 2, "id": "peer-boat-02", "turn": 5, "lobsters": 10, "score": 7100, "status": "🟢"},
        {"rank": 3, "id": "peer-boat-03", "turn": 3, "lobsters": 6, "score": 4260, "status": "🟡"},
        {"rank": 4, "id": "peer-boat-ai-01", "turn": 4, "lobsters": 8, "score": 5680, "status": "🤖"},
    ]
    
    y = 9
    for p in players:
        line = f"#{p['rank']} {p['id']:20s} Turn:{p['turn']:3d} Lobsters:{p['lobsters']:3d} Score:{p['score']:6d} {p['status']}"
        print(f"\033[{y};3H{GREEN}{line}{RESET}", end="")
        y += 1
    
    # Monster harmonics
    y += 2
    print(f"\033[{y};3H{BOLD}{MAGENTA}MONSTER HARMONICS{RESET}", end="")
    y += 1
    print(f"\033[{y};3H{'─' * (WIDTH-4)}", end="")
    y += 1
    
    shards = [
        (0, "7100 Hz", "T_2"),
        (1, "7110 Hz", "T_3"),
        (35, "7450 Hz", "T_37"),
        (70, "7800 Hz", "T_71"),
    ]
    
    for shard, freq, hecke in shards:
        line = f"Shard {shard:2d}: {freq:9s} {hecke:6s} ✅ Broadcasting"
        print(f"\033[{y};3H{MAGENTA}{line}{RESET}", end="")
        y += 1
    
    # P2P Network
    y += 2
    print(f"\033[{y};3H{BOLD}{CYAN}P2P NETWORK{RESET}", end="")
    y += 1
    print(f"\033[{y};3H{'─' * (WIDTH-4)}", end="")
    y += 1
    print(f"\033[{y};3H{CYAN}Peers: 4 | Convergence: 3 rounds | Messages: 18 | Latency: 300ms{RESET}", end="")
    
    # MCTS AI
    y += 2
    print(f"\033[{y};3H{BOLD}{YELLOW}MCTS AI-LIFE{RESET}", end="")
    y += 1
    print(f"\033[{y};3H{'─' * (WIDTH-4)}", end="")
    y += 1
    print(f"\033[{y};3H{YELLOW}Generation: 10 | Memes: 71 | Fitness: 0.8542 | Stage: Aether{RESET}", end="")
    
    # Footer
    draw_box(1, HEIGHT-5, WIDTH, 6)
    center_text(HEIGHT-4, f"{BOLD}{GREEN}[P]lay [E]volve [G]ossip [Q]uit{RESET}")
    center_text(HEIGHT-2, f"{YELLOW}QED 🔮⚡📻🦞{RESET}")
    
    sys.stdout.flush()

def animate():
    """Animate the BBS"""
    try:
        while True:
            draw_bbs()
            time.sleep(2)
    except KeyboardInterrupt:
        clear()
        center_text(HEIGHT//2, f"{GREEN}Thanks for playing TradeWars! 🔮⚡📻🦞{RESET}")
        print("\n")
        sys.exit(0)

if __name__ == "__main__":
    animate()
