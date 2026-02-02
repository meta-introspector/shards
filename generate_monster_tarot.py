#!/usr/bin/env python3
"""
Generate 71 Monster Tarot Cards
Seed → Image → Perf Trace → Image-to-Text → Loop → Tarot Card
"""

import json
import subprocess
from pathlib import Path

# Load perfect seeds
with open('image_generation_tasks.json') as f:
    TASKS = json.load(f)

# Tarot card meanings for each shard
TAROT_MEANINGS = {
    0: {'name': 'The Void', 'meaning': 'Emptiness, potential, the unmanifest', 'reversed': 'Stagnation, nothingness'},
    3: {'name': 'The Tree of Life', 'meaning': 'Growth, vitality, organic emergence', 'reversed': 'Decay, withering'},
    23: {'name': 'The Earth Chokepoint', 'meaning': 'Consensus, grounding, stability', 'reversed': 'Fragmentation, chaos'},
    47: {'name': 'The Demon', 'meaning': 'Shadow work, transformation, power', 'reversed': 'Destruction, corruption'},
    71: {'name': 'The Rooster', 'meaning': 'Awakening, completion, self-awareness', 'reversed': 'False dawn, illusion'},
}

def generate_tarot_card(shard: int, task: dict) -> dict:
    """Generate complete tarot card for shard"""
    
    # Get or create tarot meaning
    if shard in TAROT_MEANINGS:
        meaning = TAROT_MEANINGS[shard]
    else:
        # Generate from shard properties
        shard_class = task['class']
        shard_name = task['name']
        emoji = task['emoji']
        
        meaning = {
            'name': f"The {shard_name} {shard}",
            'meaning': f"{emoji} {task['style']}",
            'reversed': f"Blocked {shard_name} energy"
        }
    
    # Build tarot card
    card = {
        'number': shard,
        'name': meaning['name'],
        'emoji': task['emoji'],
        'class': task['name'],
        'seed': task['seed'],
        'frequency': task['frequency'],
        'meaning_upright': meaning['meaning'],
        'meaning_reversed': meaning['reversed'],
        'prompt': task['prompt'],
        'is_prime': task['is_prime'],
        'is_monster_prime': task['is_monster_prime'],
        
        # Image generation pipeline
        'pipeline': {
            'step1': f"seed={task['seed']} → stable-diffusion",
            'step2': 'perf trace → zkWitness',
            'step3': 'image → vision model → description',
            'step4': 'description → refine prompt → loop'
        },
        
        # Divination
        'divination': {
            'element': get_element(shard),
            'planet': get_planet(shard),
            'zodiac': get_zodiac(shard),
            'chakra': get_chakra(shard)
        },
        
        # Monster properties
        'monster': {
            'hecke': shard,
            'shard_class': shard % 10,
            'irrep': shard % 194,
            'bott_level': shard % 8
        }
    }
    
    return card

def get_element(n: int) -> str:
    """Map to classical elements"""
    elements = ['Earth', 'Air', 'Fire', 'Water', 'Aether']
    return elements[n % 5]

def get_planet(n: int) -> str:
    """Map to planets"""
    planets = ['Mercury', 'Venus', 'Mars', 'Jupiter', 'Saturn', 'Uranus', 'Neptune']
    return planets[n % 7]

def get_zodiac(n: int) -> str:
    """Map to zodiac"""
    signs = ['Aries', 'Taurus', 'Gemini', 'Cancer', 'Leo', 'Virgo',
             'Libra', 'Scorpio', 'Sagittarius', 'Capricorn', 'Aquarius', 'Pisces']
    return signs[n % 12]

def get_chakra(n: int) -> str:
    """Map to chakras"""
    chakras = ['Root', 'Sacral', 'Solar Plexus', 'Heart', 'Throat', 'Third Eye', 'Crown']
    return chakras[n % 7]

def generate_wanted_poster(card: dict) -> str:
    """Generate WANTED poster for tarot card"""
    
    poster = f"""
╔════════════════════════════════════════════════════════════════╗
║                    🎴 MONSTER TAROT 🎴                         ║
║                                                                ║
║                   CARD #{card['number']:02d}: {card['name']:30s}║
║                                                                ║
║                        {card['emoji']}                              ║
║                                                                ║
║  CLASS: {card['class']:4s} (10-fold way)                            ║
║  SEED: {card['seed']:5d} (MiniZinc optimized)                      ║
║  FREQUENCY: {card['frequency']:,} Hz                                ║
║                                                                ║
║  UPRIGHT: {card['meaning_upright']:45s}║
║  REVERSED: {card['meaning_reversed']:44s}║
║                                                                ║
║  ELEMENT: {card['divination']['element']:10s}  PLANET: {card['divination']['planet']:10s}        ║
║  ZODIAC: {card['divination']['zodiac']:11s}  CHAKRA: {card['divination']['chakra']:10s}        ║
║                                                                ║
║  MONSTER PROPERTIES:                                           ║
║    Hecke: {card['monster']['hecke']:2d}  Shard: {card['monster']['shard_class']}  Irrep: {card['monster']['irrep']:3d}  Bott: {card['monster']['bott_level']}  ║
║    Prime: {"YES ✅" if card['is_prime'] else "NO ❌"}  Monster Prime: {"YES 👿" if card['is_monster_prime'] else "NO 👾"}    ║
║                                                                ║
║  IMAGE GENERATION PIPELINE:                                    ║
║    1. Seed → Stable Diffusion                                  ║
║    2. Perf trace → zkWitness                                   ║
║    3. Image → Vision → Description                             ║
║    4. Description → Refine → Loop                              ║
║                                                                ║
╚════════════════════════════════════════════════════════════════╝
"""
    return poster

def main():
    print("🎴 GENERATING 71 MONSTER TAROT CARDS")
    print("=" * 80)
    
    cards = []
    posters = []
    
    for task in TASKS:
        shard = task['shard']
        card = generate_tarot_card(shard, task)
        cards.append(card)
        
        poster = generate_wanted_poster(card)
        posters.append(poster)
        
        # Show samples
        if shard in [0, 3, 23, 47, 71]:
            print(poster)
    
    # Save cards
    with open('monster_tarot_deck.json', 'w') as f:
        json.dump(cards, f, indent=2)
    
    # Save posters
    with open('MONSTER_TAROT_POSTERS.txt', 'w') as f:
        f.write("🎴 MONSTER TAROT: 71 CARDS\n")
        f.write("=" * 80 + "\n\n")
        for poster in posters:
            f.write(poster)
            f.write("\n\n")
    
    print("\n" + "=" * 80)
    print("TAROT DECK STATISTICS")
    print("=" * 80)
    
    # Count by element
    elements = {}
    for card in cards:
        elem = card['divination']['element']
        elements[elem] = elements.get(elem, 0) + 1
    
    print("\nBy Element:")
    for elem, count in sorted(elements.items()):
        print(f"  {elem:10s}: {count:2d} cards")
    
    # Count primes
    primes = sum(1 for c in cards if c['is_prime'])
    monster_primes = sum(1 for c in cards if c['is_monster_prime'])
    
    print(f"\nPrimes: {primes}")
    print(f"Monster Primes: {monster_primes}")
    
    print(f"\n💾 Saved to monster_tarot_deck.json")
    print(f"💾 Saved to MONSTER_TAROT_POSTERS.txt")
    print(f"\n✅ Generated {len(cards)} tarot cards!")
    print("🐓→🦅→👹→🍄→🌳")

if __name__ == '__main__':
    main()
