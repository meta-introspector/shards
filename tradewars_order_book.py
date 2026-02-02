#!/usr/bin/env python3
"""
TradeWars Order Book: Purchase Orders for Long Spaceflight
Entertainment, education, refueling stops for arcade delivery
"""

import json

# Monster primes for pricing
CROWN_PRIMES = [47, 59, 71]

def create_order_book():
    """Create purchase order book for spaceflight"""
    
    order_book = {
        "mission": "Deliver 71 Arcade Cabinets to Milliways",
        "agent": 71,
        "route": {
            "from": "Earth",
            "to": "Target (RA=5°, Dec=30°, 10,200 ly)",
            "distance": 16473,
            "travel_time_years": 164730,
            "refuel_stops": 7  # Every 7th waypoint (Monster prime!)
        },
        "purchase_orders": []
    }
    
    # 1. Entertainment (for long journey)
    entertainment = {
        "category": "ENTERTAINMENT",
        "items": [
            {"name": "Arcade Games (pre-loaded)", "quantity": 71, "price": 71000, "priority": 1},
            {"name": "Movie Database", "quantity": 1, "price": 5900, "priority": 2},
            {"name": "Music Library", "quantity": 1, "price": 4700, "priority": 2},
            {"name": "VR Simulations", "quantity": 47, "price": 47000, "priority": 1},
            {"name": "Books (digital)", "quantity": 196883, "price": 1968, "priority": 3}
        ],
        "total": 130568
    }
    
    # 2. Education (crew training during flight)
    education = {
        "category": "EDUCATION",
        "items": [
            {"name": "Monster Group Theory Course", "quantity": 1, "price": 7100, "priority": 1},
            {"name": "Astrophysics Training", "quantity": 1, "price": 5900, "priority": 1},
            {"name": "Arcade Repair Manuals", "quantity": 71, "price": 710, "priority": 1},
            {"name": "Exoplanet Survey Course", "quantity": 1, "price": 4700, "priority": 2},
            {"name": "Café Management Training", "quantity": 1, "price": 2300, "priority": 2}
        ],
        "total": 20710
    }
    
    # 3. Refueling (7 stops along the way)
    refueling = {
        "category": "REFUELING",
        "stops": [
            {"stop": 1, "location": "Waypoint 1", "distance": 2353, "fuel": 235300, "cost": 23530},
            {"stop": 2, "location": "Waypoint 2", "distance": 4706, "fuel": 235300, "cost": 23530},
            {"stop": 3, "location": "Waypoint 3", "distance": 7059, "fuel": 235300, "cost": 23530},
            {"stop": 4, "location": "Waypoint 4", "distance": 9412, "fuel": 235300, "cost": 23530},
            {"stop": 5, "location": "Waypoint 5", "distance": 11765, "fuel": 235300, "cost": 23530},
            {"stop": 6, "location": "Waypoint 6", "distance": 14118, "fuel": 235300, "cost": 23530},
            {"stop": 7, "location": "Waypoint 7", "distance": 16471, "fuel": 235300, "cost": 23530}
        ],
        "total_fuel": 1647100,
        "total_cost": 164710
    }
    
    # 4. Supplies (food, water, air for crew)
    supplies = {
        "category": "SUPPLIES",
        "items": [
            {"name": "Food (years)", "quantity": 164730, "price": 1647, "priority": 1},
            {"name": "Water (liters)", "quantity": 16473000, "price": 16473, "priority": 1},
            {"name": "Air (oxygen)", "quantity": 164730, "price": 1647, "priority": 1},
            {"name": "Medical Supplies", "quantity": 71, "price": 7100, "priority": 1},
            {"name": "Spare Parts", "quantity": 71, "price": 7100, "priority": 2}
        ],
        "total": 33967
    }
    
    # 5. Arcade Hardware (the cargo!)
    arcade_hardware = {
        "category": "ARCADE_HARDWARE",
        "items": [
            {"name": "Arcade Cabinets", "quantity": 71, "price": 710000, "priority": 1},
            {"name": "CRT Monitors", "quantity": 71, "price": 71000, "priority": 1},
            {"name": "Game ROMs", "quantity": 71, "price": 7100, "priority": 1},
            {"name": "Power Supplies", "quantity": 71, "price": 7100, "priority": 1},
            {"name": "Joysticks", "quantity": 142, "price": 1420, "priority": 2},
            {"name": "Buttons", "quantity": 568, "price": 568, "priority": 2}
        ],
        "total": 797188
    }
    
    # Add all to order book
    order_book["purchase_orders"] = [
        entertainment,
        education,
        refueling,
        supplies,
        arcade_hardware
    ]
    
    # Calculate grand total
    grand_total = (
        entertainment["total"] +
        education["total"] +
        refueling["total_cost"] +
        supplies["total"] +
        arcade_hardware["total"]
    )
    
    order_book["grand_total"] = grand_total
    order_book["currency"] = "MMC (Metameme Coin)"
    
    return order_book

def print_order_book(order_book):
    """Print order book"""
    
    print("📋 TRADEWARS ORDER BOOK")
    print("=" * 70)
    print()
    print(f"Mission: {order_book['mission']}")
    print(f"Agent: {order_book['agent']} (Rooster Crown 🐓)")
    print()
    print(f"Route: {order_book['route']['from']} → {order_book['route']['to']}")
    print(f"Distance: {order_book['route']['distance']:,} ly")
    print(f"Travel Time: {order_book['route']['travel_time_years']:,} years")
    print(f"Refuel Stops: {order_book['route']['refuel_stops']}")
    print()
    
    for po in order_book["purchase_orders"]:
        print(f"📦 {po['category']}")
        print("-" * 70)
        
        if "items" in po:
            for item in po["items"]:
                priority = "⭐" * item["priority"]
                print(f"  {item['name']:30s} x{item['quantity']:8,} = {item['price']:8,} MMC {priority}")
            print(f"  {'SUBTOTAL':30s} {'':10s} = {po['total']:8,} MMC")
        elif "stops" in po:
            for stop in po["stops"]:
                print(f"  Stop {stop['stop']}: {stop['location']:20s} {stop['fuel']:8,} units = {stop['cost']:8,} MMC")
            print(f"  {'TOTAL FUEL':30s} {po['total_fuel']:8,} units")
            print(f"  {'TOTAL COST':30s} {'':10s} = {po['total_cost']:8,} MMC")
        
        print()
    
    print("=" * 70)
    print(f"GRAND TOTAL: {order_book['grand_total']:,} MMC")
    print()
    print("💰 Payment: Metameme Coin (MMC)")
    print("📅 Delivery: Upon arrival at destination")
    print("⚠️  Note: Long journey requires entertainment & education!")
    print()
    print("☕🕳️🪟👁️👹🦅🐓💰")

def main():
    order_book = create_order_book()
    print_order_book(order_book)
    
    # Save
    with open("tradewars_order_book.json", "w") as f:
        json.dump(order_book, f, indent=2)
    
    print()
    print("💾 Saved to: tradewars_order_book.json")

if __name__ == "__main__":
    main()
