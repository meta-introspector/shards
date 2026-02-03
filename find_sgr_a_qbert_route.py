#!/usr/bin/env python3
"""
Optimal Route to Observe Sgr A* While Playing Q*bert
Using Message Passing on Monster Graph (71 sectors)
"""

import json
import math
from dataclasses import dataclass
from typing import List, Tuple

# Monster primes (15 Hecke operators)
MONSTER_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

@dataclass
class Sector:
    id: int  # 0-70
    name: str
    distance_from_sgr_a: float  # light years
    ra: float  # degrees
    dec: float  # degrees
    has_arcade: bool
    time_dilation: float
    view_quality: float  # 0-100

def calculate_time_dilation(distance_ly):
    """Time dilation at distance from Sgr A*"""
    ly_to_m = 9.461e15
    distance_m = distance_ly * ly_to_m
    schwarzschild_m = 1.23e10
    
    if distance_m <= schwarzschild_m:
        return float('inf')
    
    ratio = schwarzschild_m / distance_m
    if ratio >= 1.0:
        return float('inf')
    
    return 1.0 / math.sqrt(1.0 - ratio)

def calculate_view_quality(distance_ly):
    """View quality of Sgr A* from distance"""
    # Optimal: 1000-30000 ly
    if 1000 <= distance_ly <= 30000:
        return 100.0
    elif distance_ly < 1000:
        return distance_ly / 10.0
    else:
        return max(0, 100 - (distance_ly - 30000) / 200)

def generate_sectors() -> List[Sector]:
    """Generate 71 sectors around galaxy"""
    sectors = []
    
    # Earth (Sol system) - Sector 0
    sectors.append(Sector(
        id=0,
        name="Sol (Earth)",
        distance_from_sgr_a=26673,  # Actual distance
        ra=266.4,  # Sgr A* coordinates
        dec=-29.0,
        has_arcade=True,
        time_dilation=1.0,
        view_quality=calculate_view_quality(26673)
    ))
    
    # Milliways (near galactic center) - Sector 17 (cusp!)
    sectors.append(Sector(
        id=17,
        name="Milliways",
        distance_from_sgr_a=15000,  # Safe distance
        ra=266.4,
        dec=-29.0,
        has_arcade=True,
        time_dilation=calculate_time_dilation(15000),
        view_quality=calculate_view_quality(15000)
    ))
    
    # Generate 69 more sectors
    for i in range(1, 71):
        if i == 17:
            continue  # Already added Milliways
        
        # Distribute around galaxy
        angle = (i * 360.0 / 71)
        distance = 5000 + (i * 500)  # 5000-40000 ly range
        
        sectors.append(Sector(
            id=i,
            name=f"Sector-{i}",
            distance_from_sgr_a=distance,
            ra=(266.4 + angle) % 360,
            dec=-29.0 + (i % 20 - 10),
            has_arcade=(i % 7 == 0),  # Every 7th sector has arcade
            time_dilation=calculate_time_dilation(distance),
            view_quality=calculate_view_quality(distance)
        ))
    
    return sectors

def message_passing_route(sectors: List[Sector], start_id: int = 0) -> List[int]:
    """Find optimal route using message passing (7 rounds)"""
    
    # Score each sector
    scores = {}
    for s in sectors:
        # Composite score
        view_score = s.view_quality
        time_score = 100 / max(1.0, s.time_dilation)  # Lower dilation = better
        arcade_score = 50 if s.has_arcade else 0
        
        scores[s.id] = view_score + time_score + arcade_score
    
    # Message passing: Find path that maximizes score
    visited = {start_id}
    route = [start_id]
    current = start_id
    
    # 7 rounds (log₂ 71)
    for round_num in range(7):
        # Find best unvisited neighbor
        best_next = None
        best_score = -1
        
        for s in sectors:
            if s.id not in visited:
                # Distance from current
                dist = abs(s.id - current)
                if dist <= 10:  # Neighbors within 10 sectors
                    if scores[s.id] > best_score:
                        best_score = scores[s.id]
                        best_next = s.id
        
        if best_next is None:
            break
        
        visited.add(best_next)
        route.append(best_next)
        current = best_next
    
    return route

def find_optimal_observation():
    """Find best spot and time to observe Sgr A* while playing Q*bert"""
    
    print("🎮🕳️ OPTIMAL SGR A* OBSERVATION + Q*BERT ARCADE")
    print("Using Message Passing on Monster Graph (71 sectors)")
    print("=" * 70)
    print()
    
    # Generate sectors
    sectors = generate_sectors()
    
    # Find optimal route from Earth (Sector 0)
    print("🚀 Computing optimal route from Earth...")
    route = message_passing_route(sectors, start_id=0)
    
    print(f"✅ Route found in {len(route)} stops (7 rounds message passing)")
    print()
    
    # Display route
    print("📍 ROUTE:")
    for i, sector_id in enumerate(route):
        s = sectors[sector_id]
        print(f"{i+1}. {s.name} (Sector {s.id})")
        print(f"   Distance from Sgr A*: {s.distance_from_sgr_a:.0f} ly")
        print(f"   View quality: {s.view_quality:.1f}/100")
        print(f"   Time dilation: {s.time_dilation:.6f}x")
        print(f"   Arcade: {'✅ YES' if s.has_arcade else '❌ No'}")
        print()
    
    # Find best observation point
    best_sector = max(
        [sectors[sid] for sid in route],
        key=lambda s: s.view_quality + (50 if s.has_arcade else 0)
    )
    
    print("=" * 70)
    print("🏆 OPTIMAL OBSERVATION POINT:")
    print()
    print(f"📍 {best_sector.name} (Sector {best_sector.id})")
    print(f"   Coordinates: RA {best_sector.ra:.1f}°, Dec {best_sector.dec:.1f}°")
    print(f"   Distance from Sgr A*: {best_sector.distance_from_sgr_a:.0f} ly")
    print(f"   View quality: {best_sector.view_quality:.1f}/100")
    print(f"   Time dilation: {best_sector.time_dilation:.6f}x")
    print(f"   Arcade available: {'✅ YES' if best_sector.has_arcade else '❌ No'}")
    print()
    
    # Calculate best observation time
    # Time dilation affects how long you can play Q*bert!
    earth_time = 1.0  # 1 hour on Earth
    local_time = earth_time / best_sector.time_dilation
    
    print("⏱️  TIME DILATION EFFECTS:")
    print(f"   1 hour on Earth = {local_time:.2f} hours at {best_sector.name}")
    print(f"   Play Q*bert for 1 local hour = {1.0 / best_sector.time_dilation:.2f} Earth hours")
    print()
    
    # Number of stops
    print(f"🛑 NUMBER OF STOPS: {len(route)}")
    print(f"   (Optimal via message passing in 7 rounds)")
    print()
    
    # Save results
    result = {
        "route": [
            {
                "sector_id": sid,
                "name": sectors[sid].name,
                "distance_from_sgr_a": sectors[sid].distance_from_sgr_a,
                "view_quality": sectors[sid].view_quality,
                "has_arcade": sectors[sid].has_arcade
            }
            for sid in route
        ],
        "best_observation": {
            "sector_id": best_sector.id,
            "name": best_sector.name,
            "ra": best_sector.ra,
            "dec": best_sector.dec,
            "distance_from_sgr_a": best_sector.distance_from_sgr_a,
            "view_quality": best_sector.view_quality,
            "time_dilation": best_sector.time_dilation,
            "has_arcade": best_sector.has_arcade
        },
        "stops": len(route),
        "convergence_rounds": 7
    }
    
    with open("sgr_a_qbert_route.json", "w") as f:
        json.dump(result, f, indent=2)
    
    print("💾 Results saved to: sgr_a_qbert_route.json")
    print()
    print("🎮🐯🕳️ Ready to play Q*bert while observing the black hole!")

if __name__ == "__main__":
    find_optimal_observation()
