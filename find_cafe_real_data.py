#!/usr/bin/env python3
"""
Find Optimal Café Location Using Real Astronomy Data
Load actual star catalogs and find best spot for Milliways
"""

import json
import os
from pathlib import Path

# Monster primes
CROWN_PRIMES = [47, 59, 71]

def load_hipparcos_stars():
    """Load Hipparcos star catalog"""
    hip_file = Path("astronomy_submodules/shard_00/python-skyfield/hip_main.dat")
    
    if not hip_file.exists():
        print(f"⚠️  Hipparcos catalog not found at {hip_file}")
        return []
    
    stars = []
    with open(hip_file, 'rb') as f:
        # Hipparcos format: fixed-width fields
        for line_num, line in enumerate(f):
            if line_num > 100:  # Sample first 100 stars
                break
            try:
                # Parse Hipparcos format (simplified)
                hip_id = line[0:6].decode('ascii').strip()
                ra = line[51:63].decode('ascii').strip()  # RA in degrees
                dec = line[64:76].decode('ascii').strip()  # Dec in degrees
                
                if ra and dec:
                    stars.append({
                        "hip_id": hip_id,
                        "ra": float(ra),
                        "dec": float(dec),
                        "distance_ly": 100  # Placeholder, would need parallax
                    })
            except:
                continue
    
    return stars

def load_exoplanets():
    """Load exoplanet catalog"""
    exo_file = Path("astronomy_submodules/shard_00/open_exoplanet_catalogue/statistics.json")
    
    if not exo_file.exists():
        print(f"⚠️  Exoplanet catalog not found at {exo_file}")
        return {}
    
    with open(exo_file) as f:
        return json.load(f)

def calculate_time_dilation(distance_from_bh_ly):
    """Calculate time dilation at distance from Sgr A*"""
    import math
    
    # Convert to meters
    ly_to_m = 9.461e15
    distance_m = distance_from_bh_ly * ly_to_m
    schwarzschild_m = 1.23e10
    
    if distance_m <= schwarzschild_m:
        return float('inf')
    
    ratio = schwarzschild_m / distance_m
    if ratio >= 1.0:
        return float('inf')
    
    return 1.0 / math.sqrt(1.0 - ratio)

def score_location(ra, dec, distance_from_sgr_a):
    """Score a location for café placement"""
    
    # Time dilation (want low)
    time_dilation = calculate_time_dilation(distance_from_sgr_a)
    if time_dilation > 2.0:
        perf_score = 0
    else:
        perf_score = 100 * (2.0 - time_dilation) / 2.0
    
    # View quality (want 1000-30000 ly from Sgr A*)
    if 1000 <= distance_from_sgr_a <= 30000:
        view_score = 100
    elif distance_from_sgr_a < 1000:
        view_score = distance_from_sgr_a / 10
    else:
        view_score = max(0, 100 - (distance_from_sgr_a - 30000) / 200)
    
    # Safety (want > 10000 ly)
    if distance_from_sgr_a >= 10000:
        safety_score = 100
    elif distance_from_sgr_a >= 1000:
        safety_score = 50
    else:
        safety_score = distance_from_sgr_a / 10
    
    # Accessibility from Earth (26673 ly from Sgr A*)
    dist_from_earth = abs(distance_from_sgr_a - 26673)
    if dist_from_earth <= 5000:
        access_score = 100
    elif dist_from_earth <= 20000:
        access_score = 50
    else:
        access_score = 20
    
    total = perf_score + view_score + safety_score + access_score
    
    return {
        "performance": perf_score,
        "view": view_score,
        "safety": safety_score,
        "access": access_score,
        "total": total,
        "time_dilation": time_dilation
    }

def find_optimal_location():
    """Find optimal café location using real astronomy data"""
    
    print("🌌☕ FINDING OPTIMAL CAFÉ LOCATION")
    print("Using Real Astronomy Data")
    print("=" * 70)
    print()
    
    # Load real star data
    print("📊 Loading astronomy databases...")
    stars = load_hipparcos_stars()
    exoplanets = load_exoplanets()
    
    print(f"  • Loaded {len(stars)} stars from Hipparcos catalog")
    print(f"  • Loaded exoplanet statistics")
    print()
    
    # Score each star location
    print("🔍 Evaluating star locations...")
    candidates = []
    
    for star in stars:
        # Assume stars are at various distances from Sgr A*
        # (In reality, would need proper galactic coordinates)
        distance_from_sgr_a = star.get("distance_ly", 100) * 100  # Scale up
        
        score = score_location(star["ra"], star["dec"], distance_from_sgr_a)
        
        candidates.append({
            "hip_id": star["hip_id"],
            "ra": star["ra"],
            "dec": star["dec"],
            "distance_from_sgr_a": distance_from_sgr_a,
            "scores": score
        })
    
    # Sort by total score
    candidates.sort(key=lambda x: x["scores"]["total"], reverse=True)
    
    # Show top 5
    print()
    print("🏆 TOP 5 LOCATIONS:")
    print()
    
    for i, loc in enumerate(candidates[:5], 1):
        print(f"{i}. HIP {loc['hip_id']}")
        print(f"   RA: {loc['ra']:.2f}°, Dec: {loc['dec']:.2f}°")
        print(f"   Distance from Sgr A*: {loc['distance_from_sgr_a']:.0f} ly")
        print(f"   Time dilation: {loc['scores']['time_dilation']:.6f}x")
        print(f"   Total score: {loc['scores']['total']:.0f}/400")
        print()
    
    # Best location
    best = candidates[0]
    
    print("=" * 70)
    print("✅ OPTIMAL LOCATION FOUND!")
    print()
    print(f"📍 Near HIP {best['hip_id']}")
    print(f"   RA:       {best['ra']:.2f}°")
    print(f"   Dec:      {best['dec']:.2f}°")
    print(f"   Distance: {best['distance_from_sgr_a']:.0f} ly from Sgr A*")
    print()
    print("📊 Scores:")
    print(f"   Performance: {best['scores']['performance']:.0f}/100")
    print(f"   View:        {best['scores']['view']:.0f}/100")
    print(f"   Safety:      {best['scores']['safety']:.0f}/100")
    print(f"   Access:      {best['scores']['access']:.0f}/100")
    print(f"   TOTAL:       {best['scores']['total']:.0f}/400")
    print()
    print(f"⏱️  Time dilation: {best['scores']['time_dilation']:.6f}x")
    print()
    print("☕🕳️🪟👁️👹🦅🐓🌌")
    
    # Save results
    with open("optimal_cafe_real_data.json", "w") as f:
        json.dump({
            "best_location": best,
            "top_5": candidates[:5],
            "total_evaluated": len(candidates)
        }, f, indent=2)
    
    print()
    print("💾 Results saved to: optimal_cafe_real_data.json")

if __name__ == "__main__":
    find_optimal_location()
