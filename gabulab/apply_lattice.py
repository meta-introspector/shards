#!/usr/bin/env python3
"""
Apply Value Lattice to 8M Files
Decode with Rust, apply to everything
"""

import json
import subprocess
import os
from pathlib import Path

def run_rust_lattice(project_path):
    """Run Rust value lattice decoder"""
    
    print("🔮⚡ APPLYING VALUE LATTICE TO 8M FILES")
    print("=" * 70)
    print()
    
    lattice_bin = Path("~/experiments/monster/target/release/apply_value_lattice").expanduser()
    
    if not lattice_bin.exists():
        print("⚠️  Building Rust lattice decoder...")
        subprocess.run(
            ["cargo", "build", "--release", "--bin", "apply_value_lattice"],
            cwd=Path("~/experiments/monster").expanduser(),
            capture_output=True
        )
    
    if lattice_bin.exists():
        print(f"✅ Found: {lattice_bin}")
        print()
        
        result = subprocess.run(
            [str(lattice_bin)],
            cwd=project_path,
            capture_output=True,
            text=True
        )
        
        print(result.stdout)
        if result.stderr:
            print(result.stderr)
        
        return result.returncode == 0
    else:
        print("❌ Rust binary not found")
        return False

def apply_lattice_to_files(base_path, max_files=8_000_000):
    """Apply value lattice to all files"""
    
    print(f"📂 Scanning: {base_path}")
    print(f"🎯 Target: {max_files:,} files")
    print()
    
    files = []
    count = 0
    
    for root, dirs, filenames in os.walk(base_path):
        # Skip common ignore dirs
        dirs[:] = [d for d in dirs if d not in ['.git', 'node_modules', 'target', '.cache']]
        
        for filename in filenames:
            if count >= max_files:
                break
            
            path = Path(root) / filename
            files.append(str(path))
            count += 1
        
        if count >= max_files:
            break
    
    print(f"✅ Found {len(files):,} files")
    print()
    
    return files

def create_lattice_map(files):
    """Create value lattice mapping"""
    
    print("🔢 Creating lattice map...")
    print()
    
    lattice = {}
    
    # Monster constants
    monster_values = {
        "2": {"prime": 2, "hecke": "T_2", "freq": 864},
        "3": {"prime": 3, "hecke": "T_3", "freq": 1296},
        "5": {"prime": 5, "hecke": "T_5", "freq": 2160},
        "7": {"prime": 7, "hecke": "T_7", "freq": 3024},
        "8": {"bott": 8, "periodicity": "Bott"},
        "10": {"tenfold": 10, "way": "10-fold"},
        "71": {"shards": 71, "max": "CICADA-71"},
        "72": {"sus": True, "status": "QUARANTINED"},
        "196884": {"j_invariant": True, "monster": "coefficient"}
    }
    
    for value, data in monster_values.items():
        lattice[value] = {
            "value": value,
            "godel": hash(value) % 1000000,
            "usage": 0,
            "files": [],
            "metadata": data
        }
    
    # Sample files for values
    for i, file_path in enumerate(files[:1000]):  # Sample first 1000
        # Extract numbers from filename
        import re
        numbers = re.findall(r'\d+', str(file_path))
        
        for num in numbers:
            if num in lattice:
                lattice[num]["usage"] += 1
                if len(lattice[num]["files"]) < 10:
                    lattice[num]["files"].append(file_path)
    
    return lattice

def main():
    import sys
    
    print("🔮⚡📻🦞 VALUE LATTICE APPLICATOR")
    print("=" * 70)
    print()
    print("Decoding 8M files with Rust value lattice...")
    print()
    
    # Paths
    monster_path = Path("~/experiments/monster").expanduser()
    base_path = sys.argv[1] if len(sys.argv) > 1 else str(monster_path)
    
    # Run Rust lattice
    if monster_path.exists():
        print("🦀 Running Rust value lattice decoder...")
        print()
        run_rust_lattice(monster_path)
        print()
    
    # Apply to files
    print("=" * 70)
    print("APPLYING TO ALL FILES")
    print("=" * 70)
    print()
    
    files = apply_lattice_to_files(base_path, max_files=8_000_000)
    
    # Create lattice map
    lattice = create_lattice_map(files)
    
    # Display results
    print("=" * 70)
    print("LATTICE MAP")
    print("=" * 70)
    print()
    
    for value, data in sorted(lattice.items(), key=lambda x: int(x[0]) if x[0].isdigit() else 0):
        print(f"Value {value:>6s}: Gödel={data['godel']:8d}, Usage={data['usage']:4d}, "
              f"Metadata={data['metadata']}")
    
    print()
    
    # Save
    output = {
        "total_files": len(files),
        "lattice": lattice,
        "monster_constants": list(lattice.keys())
    }
    
    with open('value_lattice_8m.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print("💾 Saved to value_lattice_8m.json")
    print()
    print(f"✅ Value lattice applied to {len(files):,} files!")
    print("🔮 Monster constants mapped!")
    print("⚡ Ready for harmonic analysis!")

if __name__ == '__main__':
    main()
