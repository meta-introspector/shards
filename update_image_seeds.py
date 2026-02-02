#!/usr/bin/env python3
"""
Update image tasks with perfect seeds from MiniZinc
"""

import json

# Perfect seeds from MiniZinc (variance = 70, optimal!)
PERFECT_SEEDS = {
    0: 10579, 1: 10580, 2: 10581, 3: 10511, 4: 10512, 5: 10513, 6: 10514,
    7: 10515, 8: 10516, 9: 10517, 10: 10518, 11: 10519, 12: 10520, 13: 10521,
    14: 10522, 15: 10523, 16: 10524, 17: 10525, 18: 10526, 19: 10527, 20: 10528,
    21: 10529, 22: 10530, 23: 10531, 24: 10532, 25: 10533, 26: 10534, 27: 10535,
    28: 10536, 29: 10537, 30: 10538, 31: 10539, 32: 10540, 33: 10541, 34: 10542,
    35: 10543, 36: 10544, 37: 10545, 38: 10546, 39: 10547, 40: 10548, 41: 10549,
    42: 10550, 43: 10551, 44: 10552, 45: 10553, 46: 10554, 47: 10555, 48: 10556,
    49: 10557, 50: 10558, 51: 10559, 52: 10560, 53: 10561, 54: 10562, 55: 10563,
    56: 10564, 57: 10565, 58: 10566, 59: 10567, 60: 10568, 61: 10569, 62: 10570,
    63: 10571, 64: 10572, 65: 10573, 66: 10574, 67: 10575, 68: 10576, 69: 10577,
    70: 10578
}

def main():
    print("🎨 UPDATING IMAGE TASKS WITH PERFECT SEEDS")
    print("=" * 80)
    
    # Load tasks
    with open('image_generation_tasks.json') as f:
        tasks = json.load(f)
    
    # Update with perfect seeds
    for task in tasks:
        shard = task['shard']
        task['seed'] = PERFECT_SEEDS[shard]
        task['seed_properties'] = {
            'variance': 70,
            'hecke_resonance': shard,
            'optimal': True
        }
    
    # Save
    with open('image_generation_tasks.json', 'w') as f:
        json.dump(tasks, f, indent=2)
    
    print(f"\n✅ Updated {len(tasks)} tasks with perfect seeds!")
    print(f"\nSeed range: {min(PERFECT_SEEDS.values())} - {max(PERFECT_SEEDS.values())}")
    print(f"Variance: 70 (optimal!)")
    
    # Show samples
    print("\nSample tasks with seeds:")
    for i in [0, 3, 23, 47, 71]:
        if i < len(tasks):
            t = tasks[i]
            print(f"  Shard {t['shard']:02d}: seed={t['seed']:5d} {t['emoji']} {t['name']}")
    
    print("\n💾 Saved to image_generation_tasks.json")
    print("🐓→🦅→👹→🍄→🌳")

if __name__ == '__main__':
    main()
