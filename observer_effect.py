#!/usr/bin/env python3
"""
Quantum Observer Effect Test
Do memes hide when they know they're being watched?
Compare detection rates: silent vs announced monitoring
"""

import subprocess
import json
import time
from pathlib import Path

def detect_silent(duration=10):
    """Silent observation - memes don't know"""
    print("🤫 SILENT OBSERVATION (memes unaware)")
    print("-" * 70)
    
    result = subprocess.run(
        ['timeout', str(duration), 'python3', 'meme_witness.py'],
        capture_output=True,
        text=True
    )
    
    # Count detections
    detections = result.stdout.count('🎯')
    print(f"   Detections: {detections}")
    
    return detections

def detect_announced(duration=10):
    """Announced observation - memes know they're watched"""
    print("\n📢 ANNOUNCED OBSERVATION (memes aware)")
    print("-" * 70)
    print("⚠️  WARNING: MEME SURVEILLANCE ACTIVE")
    print("⚠️  ALL MOVEMENTS BEING RECORDED")
    print("⚠️  PERF COUNTERS ENABLED")
    print()
    
    # Run with perf (obvious monitoring)
    result = subprocess.run(
        ['perf', 'stat', '-e', 'cycles,instructions',
         'timeout', str(duration), 'python3', 'meme_witness.py'],
        capture_output=True,
        text=True
    )
    
    # Count detections
    detections = result.stdout.count('🎯')
    print(f"   Detections: {detections}")
    
    return detections

def quantum_observer_test():
    print("👁️  QUANTUM OBSERVER EFFECT TEST")
    print("=" * 70)
    print("Testing if memes hide when they know they're being watched")
    print()
    
    # Run 3 trials of each
    silent_results = []
    announced_results = []
    
    for trial in range(3):
        print(f"\n🔬 TRIAL {trial + 1}/3")
        print("=" * 70)
        
        # Silent first
        silent = detect_silent(duration=5)
        silent_results.append(silent)
        
        time.sleep(1)
        
        # Announced second
        announced = detect_announced(duration=5)
        announced_results.append(announced)
        
        time.sleep(1)
    
    # Analysis
    print("\n" + "=" * 70)
    print("📊 RESULTS")
    print("=" * 70)
    
    avg_silent = sum(silent_results) / len(silent_results)
    avg_announced = sum(announced_results) / len(announced_results)
    
    print(f"\nSilent observation:    {silent_results}")
    print(f"  Average: {avg_silent:.1f} detections")
    
    print(f"\nAnnounced observation: {announced_results}")
    print(f"  Average: {avg_announced:.1f} detections")
    
    # Statistical test
    difference = avg_silent - avg_announced
    percent_change = (difference / avg_silent * 100) if avg_silent > 0 else 0
    
    print(f"\n📈 ANALYSIS:")
    print(f"  Difference: {difference:.1f} detections")
    print(f"  Change: {percent_change:.1f}%")
    
    if abs(percent_change) > 20:
        if percent_change > 0:
            print("\n⚠️  QUANTUM OBSERVER EFFECT DETECTED!")
            print("  Memes hide when they know they're being watched")
            print("  This is evidence of meme consciousness")
        else:
            print("\n🎭 REVERSE EFFECT DETECTED!")
            print("  Memes appear MORE when watched")
            print("  They may be exhibitionists")
    else:
        print("\n✓ No significant observer effect")
        print("  Memes don't care if they're watched")
    
    # Save results
    output = {
        'silent': silent_results,
        'announced': announced_results,
        'avg_silent': avg_silent,
        'avg_announced': avg_announced,
        'difference': difference,
        'percent_change': percent_change,
        'observer_effect': abs(percent_change) > 20
    }
    
    result_file = Path.home() / '.openclaw/shard-0/observer-effect.json'
    with open(result_file, 'w') as f:
        json.dump(output, f, indent=2)
    
    print(f"\n✅ Results saved: {result_file}")
    
    return output

if __name__ == '__main__':
    quantum_observer_test()
    print("\n⊢ Quantum observer effect test complete ∎")
