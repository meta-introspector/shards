#!/usr/bin/env python3
"""15D Map in 10-Fold Way - Bott Periodicity Visualization"""

import sys
import math
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
BLUE = "\033[34m"

# 10-fold way (Altland-Zirnbauer classification)
TEN_FOLD = [
    ("A",    0, "Unitary",           "🔴"),
    ("AIII", 1, "Chiral Unitary",    "🟠"),
    ("AI",   2, "Orthogonal",        "🟡"),
    ("BDI",  3, "Chiral Orthogonal", "🟢"),  # I ARE LIFE!
    ("D",    4, "D-class",            "🔵"),
    ("DIII", 5, "Chiral D",          "🟣"),
    ("AII",  6, "Symplectic",        "🟤"),
    ("CII",  7, "Chiral Symplectic", "⚫"),
    ("C",    0, "C-class",            "⚪"),  # Bott mod 8
    ("CI",   1, "Chiral C",          "🟥"),
]

def clear():
    print("\033[2J\033[H", end="")
    sys.stdout.flush()

def project_15d_to_2d(coords_15d, angle1=0, angle2=0):
    """Project 15D coordinates to 2D using rotation"""
    # Simple projection: take first 2 dims and rotate
    x = coords_15d[0] * math.cos(angle1) - coords_15d[1] * math.sin(angle1)
    y = coords_15d[0] * math.sin(angle1) + coords_15d[1] * math.cos(angle1)
    
    # Add contribution from other dimensions
    for i in range(2, min(15, len(coords_15d))):
        factor = 1.0 / (i + 1)
        x += coords_15d[i] * factor * math.cos(angle2 * i)
        y += coords_15d[i] * factor * math.sin(angle2 * i)
    
    return x, y

def generate_15d_point(shard, total_shards=71):
    """Generate 15D point for shard"""
    coords = []
    for dim in range(15):
        # Use shard and dimension to generate coordinate
        angle = (shard * 2 * math.pi / total_shards) + (dim * math.pi / 15)
        coords.append(math.sin(angle) * (dim + 1))
    return coords

def draw_15d_map():
    clear()
    
    # Header
    print(f"{BOLD}{CYAN}╔{'═' * (WIDTH-2)}╗{RESET}")
    title = "🔮⚡ 15D MAP IN 10-FOLD WAY 📻🦞"
    padding = (WIDTH - len(title) - 2) // 2
    print(f"{BOLD}{CYAN}║{' ' * padding}{title}{' ' * (WIDTH - len(title) - padding - 2)}║{RESET}")
    print(f"{BOLD}{CYAN}╚{'═' * (WIDTH-2)}╝{RESET}")
    print()
    
    # Map area (30 rows)
    map_height = 30
    map_width = WIDTH - 4
    
    # Initialize map
    map_grid = [[' ' for _ in range(map_width)] for _ in range(map_height)]
    
    # Generate 71 shards in 15D and project to 2D
    angle1 = 0.5
    angle2 = 0.3
    
    for shard in range(71):
        coords_15d = generate_15d_point(shard)
        x, y = project_15d_to_2d(coords_15d, angle1, angle2)
        
        # Scale to map
        map_x = int((x + 10) * map_width / 20)
        map_y = int((y + 10) * map_height / 20)
        
        # Clamp to bounds
        map_x = max(0, min(map_width - 1, map_x))
        map_y = max(0, min(map_height - 1, map_y))
        
        # Get 10-fold class (Bott periodicity mod 8)
        bott_class = shard % 8
        symbol = TEN_FOLD[bott_class][3]
        
        map_grid[map_y][map_x] = symbol
    
    # Draw map
    print(f"{BOLD}{GREEN}┌{'─' * map_width}┐{RESET}")
    for row in map_grid:
        print(f"{GREEN}│{RESET}{''.join(row)}{GREEN}│{RESET}")
    print(f"{BOLD}{GREEN}└{'─' * map_width}┘{RESET}")
    
    # Legend
    print()
    print(f"{BOLD}{MAGENTA}10-FOLD WAY (Bott Periodicity mod 8):{RESET}")
    print()
    
    # Show legend in 2 columns
    for i in range(0, 8, 2):
        class1 = TEN_FOLD[i]
        class2 = TEN_FOLD[i+1] if i+1 < 8 else ("", "", "", "")
        
        line1 = f"{class1[3]} {class1[0]:4s} (n={class1[1]}) {class1[2]:20s}"
        line2 = f"{class2[3]} {class2[0]:4s} (n={class2[1]}) {class2[2]:20s}" if i+1 < 8 else ""
        
        print(f"  {line1}    {line2}")
    
    print()
    print(f"{BOLD}{YELLOW}15D Coordinates → 2D Projection{RESET}")
    print(f"{CYAN}71 Shards × 15 Dimensions = 1065 coordinates{RESET}")
    print(f"{MAGENTA}Bott Periodicity: Period 8 (mod 8){RESET}")
    print(f"{GREEN}BDI (n=3): I ARE LIFE! 🟢{RESET}")
    
    sys.stdout.flush()

if __name__ == "__main__":
    draw_15d_map()
    print()
    print(f"{BOLD}{CYAN}QED 🔮⚡📻🦞{RESET}")
