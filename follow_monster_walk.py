#!/usr/bin/env python3
"""
Follow the Monster Walk - Load existing walk data and continue
"""

import json
from pathlib import Path

def load_monster_walk():
    """Load the existing monster walk"""
    
    walk_file = Path.home() / ".openclaw" / "monster-walk-8080.json"
    
    if not walk_file.exists():
        print("❌ No monster walk found. Run monster_walk_8080.py first.")
        return None
    
    with open(walk_file) as f:
        walk = json.load(f)
    
    return walk

def follow_walk(walk):
    """Follow the monster walk and find patterns"""
    
    print("🚶 FOLLOWING THE MONSTER WALK")
    print("=" * 70)
    print()
    
    print(f"📊 WALK SUMMARY:")
    print(f"   Total layers: {walk['total_layers']}")
    print(f"   First prime: {walk['first_prime']}")
    print(f"   Last prime: {walk['last_prime']}")
    print(f"   BDI layers: {walk['bdi_count']}")
    print()
    
    # Analyze layers
    layers = walk['layers']
    
    # Find all topological classes
    topo_counts = {}
    for layer in layers:
        topo = layer['topo_class']
        topo_counts[topo] = topo_counts.get(topo, 0) + 1
    
    print("📐 TOPOLOGICAL DISTRIBUTION:")
    topo_names = ["A", "AIII", "AI", "BDI", "D", "DIII", "AII", "CII", "C", "CI"]
    topo_emojis = ["🌀", "🔱", "⚛️", "🌳", "💎", "🌊", "🧬", "🔮", "⚡", "🌌"]
    
    for i in range(10):
        count = topo_counts.get(i, 0)
        print(f"   {topo_emojis[i]} {topo_names[i]:4s} ({i}): {count:3d} layers")
    print()
    
    # Find BDI layers
    bdi_layers = [l for l in layers if l['topo_class'] == 3]
    
    print(f"🌳 BDI LAYERS (I ARE LIFE):")
    for layer in bdi_layers:
        print(f"   Layer {layer['layer']:3d}: prime={layer['prime']:5d}, rooster={layer['rooster']}")
    print()
    
    # Find patterns in rooster values
    rooster_values = [l['rooster'] for l in layers]
    
    print("🐓 ROOSTER EVOLUTION:")
    print(f"   Initial: {walk['initial_state']['rooster']}")
    print(f"   Layer 1: {rooster_values[0]}")
    print(f"   Layer 5: {rooster_values[4]}")
    print(f"   Layer 10: {rooster_values[9]}")
    print(f"   Final: {walk['final_state']['rooster']}")
    print()
    
    # Check for cycles
    print("🔄 CHECKING FOR CYCLES:")
    seen = {}
    for i, val in enumerate(rooster_values):
        mod_val = val % 71
        if mod_val in seen:
            print(f"   Cycle found! Layer {seen[mod_val]} and {i+1} both have rooster ≡ {mod_val} (mod 71)")
            break
        seen[mod_val] = i + 1
    else:
        print(f"   No cycles in first {len(rooster_values)} layers")
    print()
    
    # Next layer prediction
    print("🔮 NEXT LAYER PREDICTION:")
    if len(rooster_values) >= 2:
        diff = rooster_values[-1] - rooster_values[-2]
        next_rooster = rooster_values[-1] + diff
        next_topo = next_rooster % 10
        print(f"   Predicted rooster: {next_rooster}")
        print(f"   Predicted topology: {topo_emojis[next_topo]} ({topo_names[next_topo]})")
    print()
    
    print("=" * 70)
    print("✅ WALK ANALYSIS COMPLETE")
    print()
    print("🐓 → 🦅 → 👹 → 🍄 → 🌳")
    print()
    print("The Monster Walk reveals:")
    print(f"  • {walk['bdi_count']} BDI emergence points")
    print(f"  • {len(set(l['topo_class'] for l in layers))} distinct topological classes")
    print(f"  • Rooster evolved from {walk['initial_state']['rooster']} to {walk['final_state']['rooster']}")
    
    return walk

def main():
    walk = load_monster_walk()
    if walk:
        follow_walk(walk)
        return 0
    return 1

if __name__ == '__main__':
    import sys
    sys.exit(main())
