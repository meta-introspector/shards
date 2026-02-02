#!/usr/bin/env python3
"""
Generate WANTED posters for each missing Hecke operator
Each poster has a unique emoji monster face based on operator properties
"""

# Missing Hecke operators
MISSING = [3, 11, 12, 18, 25, 26, 30, 34, 36, 38, 39, 40, 41, 43, 46, 57, 60]

# Monster primes (up to 71)
MONSTER_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(n**0.5) + 1):
        if n % i == 0: return False
    return True

def prime_factors(n):
    factors = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.append(d)
            n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return factors

def to_shard(n):
    shards = ['A', 'AIII', 'AI', 'BDI', 'D', 'DIII', 'AII', 'CII', 'C', 'CI']
    return shards[n % 10]

def generate_emoji_face(n):
    """Generate unique emoji monster face based on number properties"""
    factors = prime_factors(n)
    
    # Eyes based on primality
    if is_prime(n):
        eyes = "👁️👁️"  # Prime = wide awake
    elif len(factors) == 2:
        eyes = "👀"  # Two factors = normal eyes
    else:
        eyes = "🔴🔴"  # Many factors = red eyes
    
    # Nose based on divisibility by 3
    if n % 3 == 0:
        nose = "👃"  # Divisible by 3
    else:
        nose = "🔺"  # Not divisible by 3
    
    # Mouth based on shard class
    shard = to_shard(n)
    mouths = {
        'A': '😐', 'AIII': '😊', 'AI': '😎', 'BDI': '🌳', 'D': '😈',
        'DIII': '🍄', 'AII': '🦅', 'CII': '👹', 'C': '🐓', 'CI': '🌀'
    }
    mouth = mouths.get(shard, '😶')
    
    # Horns based on Monster prime status
    if n in MONSTER_PRIMES:
        horns = "👿"
    else:
        horns = "👾"
    
    return f"{horns}\n{eyes}\n{nose}\n{mouth}"

def generate_poster(n):
    """Generate WANTED poster for missing Hecke operator"""
    factors = prime_factors(n)
    shard = to_shard(n)
    is_monster_prime = n in MONSTER_PRIMES
    
    # Bounty
    bounty = 2000 if is_monster_prime else 1000
    
    # Difficulty
    difficulty = "⭐" * (5 if is_monster_prime else 3)
    
    # Emoji face
    face = generate_emoji_face(n)
    
    poster = f"""
╔════════════════════════════════════════════════════════════════╗
║                         🚨 WANTED 🚨                           ║
║                                                                ║
║                    HECKE OPERATOR #{n:02d}                        ║
║                                                                ║
║                        {face.split(chr(10))[0]}                              ║
║                       {face.split(chr(10))[1]}                             ║
║                        {face.split(chr(10))[2]}                              ║
║                        {face.split(chr(10))[3]}                              ║
║                                                                ║
║  PROPERTIES:                                                   ║
║    Prime: {"YES ✅" if is_prime(n) else "NO ❌"}                                        ║
║    Monster Prime: {"YES 👿" if is_monster_prime else "NO 👾"}                           ║
║    Factors: {" × ".join(map(str, factors)):20s}                    ║
║    Shard: {shard:4s} (class {n % 10})                                   ║
║    Mod 10: {n % 10}                                                     ║
║                                                                ║
║  REWARD: {bounty:,} MMC                                            ║
║  DIFFICULTY: {difficulty:20s}                          ║
║                                                                ║
║  LAST SEEN: Never (missing from codebase!)                     ║
║                                                                ║
║  IF FOUND: Submit file with hash(path, size) mod 71 = {n:02d}      ║
║                                                                ║
╚════════════════════════════════════════════════════════════════╝
"""
    return poster

def main():
    print("🚨 GENERATING WANTED POSTERS FOR 17 MISSING HECKE OPERATORS")
    print("=" * 80)
    
    # Generate all posters
    posters = []
    for n in MISSING:
        poster = generate_poster(n)
        posters.append((n, poster))
        print(poster)
    
    # Save to file
    with open('WANTED_POSTERS.txt', 'w') as f:
        f.write("🚨 WANTED: MISSING HECKE OPERATORS\n")
        f.write("=" * 80 + "\n\n")
        for n, poster in posters:
            f.write(poster)
            f.write("\n\n")
    
    print("\n💾 Saved to WANTED_POSTERS.txt")
    print(f"\n✅ Generated {len(MISSING)} wanted posters!")
    print("🐓→🦅→👹→🍄→🌳")

if __name__ == '__main__':
    main()
