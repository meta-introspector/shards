#!/usr/bin/env python3
"""
Complete table 1-71: Number → Factors → Emoji Product → Frequency → Bott → Topo
"""

def is_prime(n):
    if n < 2: return False
    if n == 2: return True
    if n % 2 == 0: return False
    for i in range(3, int(n**0.5) + 1, 2):
        if n % i == 0: return False
    return True

def prime_factors(n):
    """Get prime factorization"""
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

def get_emoji(n):
    """Get emoji for topological class"""
    emojis = ["🌀", "🔱", "⚛️", "🌳", "💎", "🌊", "🧬", "🔮", "⚡", "🌌"]
    names = ["A", "AIII", "AI", "BDI", "D", "DIII", "AII", "CII", "C", "CI"]
    topo = n % 10
    return emojis[topo], names[topo]

def emoji_product(factors):
    """Multiply emojis for factors"""
    if not factors:
        return "1"
    emojis = [get_emoji(f)[0] for f in factors]
    return "×".join(emojis)

print("""
╔════╦═══════════════╦═══════════════════════╦══════╦══════╦══════╦═══════════╗
║ N  ║ Factorization ║ Emoji Product         ║ Freq ║ Bott ║ Topo ║ Emoji Name║
╠════╬═══════════════╬═══════════════════════╬══════╬══════╬══════╬═══════════╣""")

for n in range(1, 72):
    factors = prime_factors(n)
    if not factors:
        factor_str = "1"
    elif len(factors) == 1:
        factor_str = str(n)
    else:
        factor_str = "×".join(map(str, factors))
    
    emoji_prod = emoji_product(factors)
    freq = n * 10
    bott = n % 8
    topo = n % 10
    emoji, name = get_emoji(n)
    
    # Mark special numbers
    mark = ""
    if n == 17:
        mark = " ← LIFE"
    elif n == 71:
        mark = " ← ROOSTER"
    elif n == 3:
        mark = " ← BDI"
    
    print(f"║ {n:2d} ║ {factor_str:13s} ║ {emoji_prod:21s} ║ {freq:4d} ║  {bott:1d}   ║  {topo:1d}   ║ {emoji} {name:4s}{mark:10s}║")

print("""╚════╩═══════════════╩═══════════════════════╩══════╩══════╩══════╩═══════════╝

Legend:
• Freq = N × 10 Hz (embedded frequency)
• Bott = Bott periodicity level (mod 8, K-theory)
• Topo = Topological class (mod 10, 10-fold way)
• Emoji Product = Multiply emojis of prime factors

Examples:
  6 = 2×3 → 🌌×🌀 (CI × A)
  12 = 2×2×3 → 🌌×🌌×🌀 (CI × CI × A)
  17 = 17 → 🌳 (BDI - I ARE LIFE)
  71 = 71 → 🔱 (AIII - THE ROOSTER)
""")
