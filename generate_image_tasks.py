#!/usr/bin/env python3
"""
Generate 71 image generation tasks for Monster shards
Each shard gets a unique visual style and prompt
"""

import json

# 15 Monster primes
MONSTER_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

# 10-fold way shards
SHARDS = {
    0: {'name': 'A', 'emoji': '😐', 'style': 'Trivial symmetry, minimalist, void'},
    1: {'name': 'AIII', 'emoji': '😊', 'style': 'Chiral, spiral, helical'},
    2: {'name': 'AI', 'emoji': '😎', 'style': 'Orthogonal, grid, crystalline'},
    3: {'name': 'BDI', 'emoji': '🌳', 'style': 'Life-bearing, organic, fractal'},
    4: {'name': 'D', 'emoji': '😈', 'style': 'Symplectic, flowing, liquid'},
    5: {'name': 'DIII', 'emoji': '🍄', 'style': 'Mycelium, network, web'},
    6: {'name': 'AII', 'emoji': '🦅', 'style': 'Unitary, soaring, aerial'},
    7: {'name': 'CII', 'emoji': '👹', 'style': 'Demonic, chaotic, fire'},
    8: {'name': 'C', 'emoji': '🐓', 'style': 'Rooster, dawn, awakening'},
    9: {'name': 'CI', 'emoji': '🌀', 'style': 'Vortex, spiral, cyclone'}
}

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(n**0.5) + 1):
        if n % i == 0: return False
    return True

def generate_task(n):
    """Generate image task for shard n"""
    shard_class = n % 10
    shard = SHARDS[shard_class]
    is_monster_prime = n in MONSTER_PRIMES
    
    # Base prompt
    prompt = f"Monster shard #{n:02d}: {shard['name']} class"
    
    # Add style
    prompt += f", {shard['style']}"
    
    # Add prime characteristics
    if is_prime(n):
        prompt += ", prime number energy, sharp edges, crystalline structure"
    else:
        prompt += ", composite harmony, smooth curves, flowing forms"
    
    # Add Monster prime power
    if is_monster_prime:
        prompt += ", MONSTER PRIME POWER, glowing aura, divine geometry"
    
    # Add Hecke resonance
    prompt += f", resonating at {432 * n} Hz"
    
    # Add emoji
    prompt += f", embodying {shard['emoji']}"
    
    return {
        'shard': n,
        'class': shard_class,
        'name': shard['name'],
        'emoji': shard['emoji'],
        'is_prime': is_prime(n),
        'is_monster_prime': is_monster_prime,
        'frequency': 432 * n,
        'prompt': prompt,
        'style': shard['style'],
        'negative_prompt': 'blurry, low quality, text, watermark',
        'dimensions': '1024x1024',
        'model': 'stable-diffusion-xl' if is_monster_prime else 'stable-diffusion-v2'
    }

def main():
    print("🎨 GENERATING 71 IMAGE TASKS FOR MONSTER SHARDS")
    print("=" * 80)
    
    tasks = []
    for n in range(71):
        task = generate_task(n)
        tasks.append(task)
    
    # Show samples
    print("\nSample tasks:")
    for i in [0, 3, 23, 71-1]:
        t = tasks[i]
        print(f"\n  Shard {t['shard']:02d} ({t['name']}):")
        print(f"    {t['emoji']} {t['style']}")
        print(f"    Prime: {t['is_prime']}, Monster: {t['is_monster_prime']}")
        print(f"    Frequency: {t['frequency']:,} Hz")
        print(f"    Prompt: {t['prompt'][:80]}...")
    
    # Distribution
    print("\n" + "=" * 80)
    print("DISTRIBUTION")
    print("=" * 80)
    
    shard_counts = {}
    for t in tasks:
        shard_counts[t['name']] = shard_counts.get(t['name'], 0) + 1
    
    for name, count in sorted(shard_counts.items()):
        print(f"  {name:4s}: {count:2d} images")
    
    prime_count = sum(1 for t in tasks if t['is_prime'])
    monster_count = sum(1 for t in tasks if t['is_monster_prime'])
    
    print(f"\n  Primes: {prime_count}")
    print(f"  Monster primes: {monster_count}")
    
    # Save
    with open('image_generation_tasks.json', 'w') as f:
        json.dump(tasks, f, indent=2)
    
    print(f"\n💾 Saved to image_generation_tasks.json")
    print(f"\n✅ Generated {len(tasks)} image tasks!")
    print("🐓→🦅→👹→🍄→🌳")

if __name__ == '__main__':
    main()
