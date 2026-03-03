#!/usr/bin/env python3
# Lift Nix-Wars into Zone 42 Orbit Pilot format

import json
import hashlib
from urllib.parse import quote

def escape_rdfa(text):
    """Escape text for RDFa URL encoding"""
    return quote(text, safe='')

def commitment_to_emoji(commitment):
    """Convert commitment hash to emoji sequence"""
    emoji_map = {
        '0': '🌑', '1': '🌒', '2': '🌓', '3': '🌔',
        '4': '🌕', '5': '🌖', '6': '🌗', '7': '🌘',
        '8': '⭐', '9': '✨', 'a': '🚀', 'b': '🛸',
        'c': '🌌', 'd': '🔮', 'e': '💫', 'f': '🌠'
    }
    return ''.join(emoji_map.get(c, '❓') for c in commitment[:8])

def state_to_orbit(state_file, index):
    """Convert Nix-Wars state to orbit format"""
    with open(state_file) as f:
        state = json.load(f)
    
    round_num = state.get('round', 0)
    commitment = state.get('zkperf', {}).get('commitment', '')
    ships = state.get('ships', {})
    
    # Calculate orbit position
    angle = (index / 10) * 3.14159 * 2
    radius = 200 + (round_num * 50)
    
    # Determine vibe from round
    vibe = round_num % 8
    
    orbit = {
        'label': f'Round {round_num}',
        'emoji': commitment_to_emoji(commitment) if commitment else '🌑',
        'commitment': commitment[:16] if commitment else 'genesis',
        'angle': angle,
        'radius': radius,
        'vibe': vibe,
        'ships': ships,
        'zkperf': state.get('zkperf', {})
    }
    
    return orbit

if __name__ == '__main__':
    import sys
    
    if len(sys.argv) < 2:
        print("Usage: lift-to-pilot.py <state.json> [state2.json ...]")
        sys.exit(1)
    
    orbits = []
    for i, state_file in enumerate(sys.argv[1:]):
        orbit = state_to_orbit(state_file, i)
        orbits.append(orbit)
        print(f"✨ Lifted {state_file} → Orbit {i}", file=sys.stderr)
        print(f"   Emoji: {orbit['emoji']}", file=sys.stderr)
        print(f"   Position: angle={orbit['angle']:.2f}, radius={orbit['radius']}", file=sys.stderr)
    
    print(json.dumps(orbits, indent=2))
