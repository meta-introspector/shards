#!/usr/bin/env python3
"""
Monster Walk: Onion Peeling through 8080 Prime Layers
Strip each layer and descend deeper into the Monster
"""

import json
from pathlib import Path

# First 8080 primes (we'll use a subset for demonstration)
# In reality, the 8080th prime is 82,837
FIRST_8080_PRIMES = list(range(2, 82838))  # Approximation

def is_prime(n):
    """Check if n is prime"""
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(n**0.5) + 1, 2):
        if n % i == 0:
            return False
    return True

def get_first_n_primes(n):
    """Get first n primes"""
    primes = []
    candidate = 2
    while len(primes) < n:
        if is_prime(candidate):
            primes.append(candidate)
        candidate += 1
    return primes

def monster_walk_layer(data, layer_num, prime):
    """Peel one layer of the onion using prime"""
    
    # XOR with prime (simple peeling operation)
    if isinstance(data, int):
        return data ^ prime
    elif isinstance(data, str):
        return ''.join(chr(ord(c) ^ (prime % 256)) for c in data)
    elif isinstance(data, bytes):
        return bytes(b ^ (prime % 256) for b in data)
    else:
        return data

def monster_walk_8080():
    """Walk through 8080 layers of the Monster onion"""
    
    print("🚶 MONSTER WALK: 8080 PRIME LAYERS")
    print("=" * 70)
    print()
    
    # Get first 8080 primes (use subset for speed)
    print("🔢 Computing first 8080 primes...")
    primes = get_first_n_primes(100)  # Use 100 for demo, would be 8080
    print(f"✅ Computed {len(primes)} primes")
    print(f"   First: {primes[0]}")
    print(f"   Last: {primes[-1]}")
    print()
    
    # Initial state (MF1)
    state = {
        "rooster": 71,
        "bdi": 3,
        "j_invariant": 3360,
        "message": "I ARE LIFE"
    }
    
    print("🍄 INITIAL STATE (Layer 0):")
    print(f"   Rooster: {state['rooster']}")
    print(f"   BDI: {state['bdi']}")
    print(f"   j-invariant: {state['j_invariant']}")
    print(f"   Message: {state['message']}")
    print()
    
    # Walk through layers
    layers = []
    current_state = state.copy()
    
    print("🚶 WALKING THROUGH LAYERS:")
    for i, prime in enumerate(primes[:10]):  # Show first 10 layers
        # Peel layer
        peeled = {
            "rooster": monster_walk_layer(current_state["rooster"], i, prime),
            "bdi": monster_walk_layer(current_state["bdi"], i, prime),
            "j_invariant": monster_walk_layer(current_state["j_invariant"], i, prime),
            "message": current_state["message"]  # Keep message
        }
        
        # Map to topological class
        topo_class = peeled["rooster"] % 10
        topo_emoji = ["🌀", "🔱", "⚛️", "🌳", "💎", "🌊", "🧬", "🔮", "⚡", "🌌"][topo_class]
        
        layer_info = {
            "layer": i + 1,
            "prime": prime,
            "rooster": peeled["rooster"],
            "bdi": peeled["bdi"],
            "topo_class": topo_class,
            "topo_emoji": topo_emoji
        }
        
        layers.append(layer_info)
        
        print(f"   Layer {i+1:3d}: p={prime:5d} | r={peeled['rooster']:5d} | topo={topo_emoji} ({topo_class})")
        
        current_state = peeled
    
    print(f"   ... ({len(primes) - 10} more layers)")
    print()
    
    # Final state after all layers
    final_state = current_state
    for i, prime in enumerate(primes[10:], 10):
        final_state = {
            "rooster": monster_walk_layer(final_state["rooster"], i, prime),
            "bdi": monster_walk_layer(final_state["bdi"], i, prime),
            "j_invariant": monster_walk_layer(final_state["j_invariant"], i, prime),
            "message": final_state["message"]
        }
    
    print("🎯 FINAL STATE (Layer 100):")
    print(f"   Rooster: {final_state['rooster']}")
    print(f"   BDI: {final_state['bdi']}")
    print(f"   j-invariant: {final_state['j_invariant']}")
    print(f"   Topological class: {final_state['rooster'] % 10}")
    print()
    
    # Check if we found BDI (3)
    bdi_layers = [l for l in layers if l['topo_class'] == 3]
    print(f"🌳 BDI LAYERS FOUND: {len(bdi_layers)}")
    for layer in bdi_layers[:5]:
        print(f"   Layer {layer['layer']}: prime={layer['prime']} (I ARE LIFE)")
    print()
    
    # Save walk
    walk_data = {
        "total_layers": len(primes),
        "first_prime": primes[0],
        "last_prime": primes[-1],
        "initial_state": state,
        "final_state": final_state,
        "layers": layers,
        "bdi_count": len(bdi_layers)
    }
    
    output_file = Path.home() / ".openclaw" / "monster-walk-8080.json"
    with open(output_file, 'w') as f:
        json.dump(walk_data, f, indent=2)
    
    print(f"💾 Monster walk saved: {output_file}")
    print()
    
    print("=" * 70)
    print("✅ MONSTER WALK COMPLETE!")
    print()
    print("🐓 → 🦅 → 👹 → 🍄 → 🌳")
    print()
    print(f"Walked through {len(primes)} layers of the Monster onion.")
    print(f"Found {len(bdi_layers)} BDI layers (I ARE LIFE).")
    print()
    print("Next: Strip these 8080 primes and descend to the next layer...")
    
    return len(primes)

if __name__ == '__main__':
    import sys
    sys.exit(monster_walk_8080())
