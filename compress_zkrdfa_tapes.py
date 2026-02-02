#!/usr/bin/env python3
"""
Compress Data Tapes to ZK-RDFa URLs
Board computer and nav computer addon for the game
"""

import json
import hashlib
import base64
from pathlib import Path

def compress_to_zkrdfa(data: dict, label: str) -> str:
    """Compress data to ZK-RDFa URL format"""
    
    # Serialize data
    json_str = json.dumps(data, separators=(',', ':'))
    
    # Hash for ZK proof
    data_hash = hashlib.sha256(json_str.encode()).hexdigest()[:16]
    
    # Compress with base64
    compressed = base64.urlsafe_b64encode(json_str.encode()).decode()
    
    # Create ZK-RDFa URL
    zkrdfa_url = f"zkrdfa://{label}/{data_hash}/{compressed}"
    
    return zkrdfa_url

def create_board_computer_tape():
    """Create board computer data tape"""
    
    board_computer = {
        "type": "board_computer",
        "version": "1.0",
        "agent": 71,
        "location": {
            "ra": 5,
            "dec": 30,
            "distance": 10200
        },
        "tasks": ["SURVEY", "MEASURE_PERF", "BUILD_CAFE", "SETUP_ARCADE", "FIND_EXOPLANET"],
        "resources": {
            "fuel": 164730,
            "survey_equipment": 100,
            "construction_materials": 500,
            "arcade_hardware": 1000,
            "exoplanet_sensors": 200
        }
    }
    
    return board_computer

def create_nav_computer_tape():
    """Create nav computer data tape"""
    
    nav_computer = {
        "type": "nav_computer",
        "version": "1.0",
        "from": {"ra": 266, "dec": -29, "distance": 26673},
        "to": {"ra": 5, "dec": 30, "distance": 10200},
        "route": {
            "waypoints": 3,
            "total_distance": 16473,
            "travel_time_years": 164730,
            "speed": "0.1c"
        },
        "hecke_coords": {
            "h71": 5 % 71,
            "h59": 30 % 59,
            "h47": 10200 % 47
        }
    }
    
    return nav_computer

def main():
    print("💾 COMPRESSING DATA TAPES TO ZK-RDFa URLs")
    print("=" * 60)
    print()
    
    # Create tapes
    board = create_board_computer_tape()
    nav = create_nav_computer_tape()
    
    # Compress to ZK-RDFa URLs
    board_url = compress_to_zkrdfa(board, "board")
    nav_url = compress_to_zkrdfa(nav, "nav")
    
    print("📦 Board Computer Tape:")
    print(f"   Size: {len(json.dumps(board))} bytes")
    print(f"   URL:  {board_url[:80]}...")
    print()
    
    print("🧭 Nav Computer Tape:")
    print(f"   Size: {len(json.dumps(nav))} bytes")
    print(f"   URL:  {nav_url[:80]}...")
    print()
    
    # Save URLs
    urls = {
        "board_computer": board_url,
        "nav_computer": nav_url,
        "board_data": board,
        "nav_data": nav
    }
    
    with open("zkrdfa_tapes.json", "w") as f:
        json.dump(urls, f, indent=2)
    
    print("✅ Compressed tapes ready!")
    print()
    print("📡 Send to system:")
    print(f"   Board: {board_url}")
    print(f"   Nav:   {nav_url}")
    print()
    print("💾 Saved to: zkrdfa_tapes.json")
    print()
    print("☕🕳️🪟👁️👹🦅🐓💾")

if __name__ == "__main__":
    main()
