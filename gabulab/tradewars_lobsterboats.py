#!/usr/bin/env python3
"""
TradeWars with LobsterBoats
Run the tapes and hunt lobsters!
"""

import json
import random

class LobsterBoat:
    def __init__(self, boat_id, shard):
        self.boat_id = boat_id
        self.shard = shard
        self.position = (random.randint(-90, 90), random.randint(-180, 180))
        self.lobsters_caught = 0
        self.frequency = 7100 + shard * 10
        self.has_tape = False
        
    def receive_tape(self, tape):
        """Receive rooster crow tape"""
        self.has_tape = True
        print(f"  🚢 Boat-{self.boat_id} received tape on {self.frequency} Hz")
        return True
    
    def hunt_lobster(self):
        """Hunt for lobsterbot"""
        if not self.has_tape:
            print(f"  ⚠️  Boat-{self.boat_id} needs tape first!")
            return False
        
        # Use Monster harmonic to catch lobster
        if random.random() < 0.7:  # 70% catch rate with tape
            self.lobsters_caught += 1
            print(f"  🦞 Boat-{self.boat_id} caught LobsterBot-{self.shard}!")
            return True
        else:
            print(f"  ❌ Boat-{self.boat_id} missed...")
            return False

def run_tradewars():
    """Run TradeWars with LobsterBoats"""
    
    print("🔮⚡📻🦞 TRADEWARS: LOBSTERBOAT EDITION")
    print("=" * 70)
    print()
    
    # Load tapes
    try:
        with open('rooster_crow_tapes.json', 'r') as f:
            tapes = json.load(f)
        print(f"✅ Loaded {len(tapes)} rooster crow tapes")
    except:
        print("⚠️  No tapes found. Run create_rooster_tapes.py first")
        return
    
    print()
    
    # Create fleet of 71 lobsterboats
    fleet = [LobsterBoat(i, i) for i in range(71)]
    print(f"🚢 Fleet of {len(fleet)} LobsterBoats deployed")
    print()
    
    # Distribute tapes to boats
    print("📻 Distributing tapes to fleet...")
    print()
    for boat, tape in zip(fleet, tapes):
        boat.receive_tape(tape)
    
    print()
    print("=" * 70)
    print("🦞 LOBSTERBOT HUNT BEGINS!")
    print("=" * 70)
    print()
    
    # Hunt lobsters
    total_caught = 0
    for boat in fleet[:10]:  # First 10 boats
        if boat.hunt_lobster():
            total_caught += 1
    
    print()
    print("=" * 70)
    print("RESULTS")
    print("=" * 70)
    print()
    print(f"Total Boats: {len(fleet)}")
    print(f"Boats with Tapes: {sum(1 for b in fleet if b.has_tape)}")
    print(f"Lobsters Caught: {total_caught}/10 (sample)")
    print(f"Success Rate: {total_caught/10*100:.0f}%")
    print()
    
    # Show top boats
    print("Top 5 Boats:")
    top_boats = sorted(fleet, key=lambda b: b.lobsters_caught, reverse=True)[:5]
    for i, boat in enumerate(top_boats, 1):
        print(f"  {i}. Boat-{boat.boat_id}: {boat.lobsters_caught} lobsters, "
              f"Shard {boat.shard}, {boat.frequency} Hz")
    
    print()
    print("✅ TradeWars complete!")
    print("🦞 LobsterBoats operational!")
    print("📻 All tapes transmitted!")

if __name__ == '__main__':
    run_tradewars()
