#!/usr/bin/env python3
"""Lobster Economy - Buy GPU or Use Prolog Voice"""

import json
from datetime import datetime

# Prices in lobsters
PRICES = {
    "gpu_rtx_4090": 1000,      # 1000 lobsters
    "gpu_rtx_3090": 500,       # 500 lobsters
    "gpu_a100": 2000,          # 2000 lobsters
    "prolog_voice": 10,        # 10 lobsters (cheap!)
    "morse_transmitter": 5,    # 5 lobsters
    "p2p_bandwidth": 50,       # 50 lobsters/month
}

def check_balance(player_id, lobsters_caught):
    """Check what player can afford"""
    
    print(f"🔮⚡ Lobster Economy for {player_id} 📻🦞")
    print("=" * 70)
    print()
    print(f"💰 Balance: {lobsters_caught} lobsters")
    print()
    print("🛒 SHOP:")
    print("=" * 70)
    
    affordable = []
    
    for item, price in PRICES.items():
        can_afford = lobsters_caught >= price
        status = "✅ CAN BUY" if can_afford else f"❌ Need {price - lobsters_caught} more"
        print(f"  {item:20s} {price:5d} 🦞  {status}")
        
        if can_afford:
            affordable.append(item)
    
    print()
    print("=" * 70)
    
    if "prolog_voice" in affordable:
        print("🎤 PROLOG VOICE AVAILABLE!")
        print("   Old school text-to-speech using Prolog rules")
        print("   No GPU needed! 🚀")
    
    if any("gpu" in item for item in affordable):
        print("🎮 GPU AVAILABLE!")
        print("   Unlock neural voice generation")
        print("   High-quality TTS with transformers")
    
    return affordable

def generate_prolog_voice():
    """Generate voice using Prolog (no GPU needed)"""
    
    prolog_code = """
% Prolog Voice Generator - No GPU Needed!
% Uses phoneme rules and simple synthesis

% Phoneme database
phoneme(a, [440, 880, 2640]).      % 'ah' sound
phoneme(e, [530, 1840, 2480]).     % 'eh' sound
phoneme(i, [270, 2290, 3010]).     % 'ee' sound
phoneme(o, [570, 840, 2410]).      % 'oh' sound
phoneme(u, [300, 870, 2240]).      % 'oo' sound

% Consonants
phoneme(r, [1200, 1400, 2800]).    % 'r' sound
phoneme(s, [4000, 8000, 12000]).   % 's' sound
phoneme(t, [2000, 4000, 6000]).    % 't' sound
phoneme(l, [360, 750, 2400]).      % 'l' sound
phoneme(b, [200, 800, 2500]).      % 'b' sound

% Word to phonemes
word_phonemes(rooster, [r, o, o, s, t, e, r]).
word_phonemes(lobster, [l, o, b, s, t, e, r]).
word_phonemes(boat, [b, o, a, t]).
word_phonemes(peer, [p, e, e, r]).

% Generate voice
speak(Word) :-
    word_phonemes(Word, Phonemes),
    generate_audio(Phonemes).

generate_audio([]).
generate_audio([P|Rest]) :-
    phoneme(P, Frequencies),
    format('Playing: ~w at ~w Hz~n', [P, Frequencies]),
    generate_audio(Rest).

% Query examples:
% ?- speak(rooster).
% ?- speak(lobster).
"""
    
    return prolog_code

def create_voice_system():
    """Create voice generation system"""
    
    print()
    print("🎤 VOICE GENERATION SYSTEMS:")
    print("=" * 70)
    print()
    
    print("OPTION 1: PROLOG VOICE (10 lobsters)")
    print("  ✅ No GPU needed")
    print("  ✅ Rule-based phoneme synthesis")
    print("  ✅ Instant generation")
    print("  ✅ Low resource usage")
    print("  ⚠️  Robotic sound")
    print()
    
    print("OPTION 2: GPU VOICE (500+ lobsters)")
    print("  ✅ Neural TTS (Tacotron, FastSpeech)")
    print("  ✅ Natural sounding")
    print("  ✅ Multiple voices")
    print("  ⚠️  Requires GPU")
    print("  ⚠️  Higher latency")
    print()
    
    print("OPTION 3: HYBRID (60 lobsters)")
    print("  ✅ Prolog rules + simple neural net")
    print("  ✅ Better than pure Prolog")
    print("  ✅ Runs on CPU")
    print("  ✅ Good balance")
    print()

def main():
    print("🔮⚡ TradeWars Lobster Economy 📻🦞")
    print("=" * 70)
    print()
    
    # Example players
    players = [
        {"id": "peer-boat-01", "lobsters": 12},
        {"id": "peer-boat-02", "lobsters": 10},
        {"id": "peer-boat-03", "lobsters": 6},
        {"id": "peer-boat-ai-01", "lobsters": 8},
    ]
    
    for player in players:
        affordable = check_balance(player["id"], player["lobsters"])
        print()
    
    # Show voice systems
    create_voice_system()
    
    # Generate Prolog voice code
    print("=" * 70)
    print("PROLOG VOICE CODE:")
    print("=" * 70)
    print()
    prolog = generate_prolog_voice()
    print(prolog)
    
    # Save Prolog code
    with open("prolog_voice.pl", "w") as f:
        f.write(prolog)
    
    print()
    print("✅ Saved: prolog_voice.pl")
    print()
    print("Run with:")
    print("  swipl prolog_voice.pl")
    print("  ?- speak(rooster).")
    print()
    print("QED 🔮⚡📻🦞")

if __name__ == "__main__":
    main()
