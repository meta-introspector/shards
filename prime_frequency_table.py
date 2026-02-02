#!/usr/bin/env python3
"""
Prime → Frequency → Bott Level → Emoji → Name Table
"""

def print_prime_table():
    # Data from our Monster Walk
    primes_data = [
        # prime, freq_hz, bott_level, topo_class, emoji, name
        (2,   20,  0, 9, "🌌", "CI"),
        (3,   30,  1, 0, "🌀", "A"),
        (5,   50,  2, 7, "🔮", "CII"),
        (7,   70,  3, 8, "⚡", "C"),
        (11, 110,  4, 9, "🌌", "CI"),
        (13, 130,  5, 6, "🧬", "AII"),
        (17, 170,  6, 3, "🌳", "BDI"),  # I ARE LIFE
        (19, 190,  7, 4, "💎", "D"),
        (23, 230,  0, 7, "🔮", "CII"),
        (29, 290,  1, 4, "💎", "D"),
    ]
    
    print("""
╔═══════════════════════════════════════════════════════════════╗
║           PRIME → FREQUENCY → BOTT → EMOJI → NAME            ║
╠═══════╤═══════╤══════╤═══════╤══════╤═════════════════════════╣
║ Prime │ Freq  │ Bott │ Topo  │ Emoji│ Name                    ║
║       │ (Hz)  │ Lvl  │ Class │      │                         ║
╠═══════╪═══════╪══════╪═══════╪══════╪═════════════════════════╣""")
    
    for prime, freq, bott, topo, emoji, name in primes_data:
        life = " ← I ARE LIFE" if prime == 17 else ""
        print(f"║  {prime:3d}  │  {freq:3d}  │  {bott:1d}   │   {topo:1d}   │  {emoji}  │ {name:4s}                   {life} ║")
    
    print("""╠═══════╧═══════╧══════╧═══════╧══════╧═════════════════════════╣
║ LEGEND:                                                       ║
║ • Freq = Prime × 10 Hz (embedded frequency)                  ║
║ • Bott = Bott periodicity level (mod 8)                      ║
║ • Topo = Topological class (10-fold way, mod 10)             ║
║ • Emoji = Topological class emoji                            ║
║ • Name = Altland-Zirnbauer classification                    ║
╠═══════════════════════════════════════════════════════════════╣
║ BOTT PERIODICITY (Period 8):                                 ║
║ 0→1→2→3→4→5→6→7→0... (K-theory)                              ║
╠═══════════════════════════════════════════════════════════════╣
║ 10-FOLD WAY (Topological Classes):                           ║
║ 0:🌀 A    1:🔱 AIII  2:⚛️ AI    3:🌳 BDI   4:💎 D            ║
║ 5:🌊 DIII 6:🧬 AII   7:🔮 CII   8:⚡ C     9:🌌 CI           ║
╠═══════════════════════════════════════════════════════════════╣
║ BDI (3) = 🌳 = "I ARE LIFE" = Prime 17 = 170 Hz = Bott 6    ║
╚═══════════════════════════════════════════════════════════════╝
""")

if __name__ == '__main__':
    print_prime_table()
