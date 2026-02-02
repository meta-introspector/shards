#!/usr/bin/env python3
"""Extract magic numbers from LMFDB: tau function, j-invariant, Monster constants"""
import json
import os
from pathlib import Path
from collections import defaultdict

# Magic numbers we're hunting
MAGIC_NUMBERS = {
    # Monster Group
    'monster_order': 808017424794512875886459904961710757005754368000000000,
    'monster_dim': 196884,  # Smallest faithful rep
    'j_invariant_196884': 196884,  # j(τ) = q^-1 + 744 + 196884q + ...
    'j_constant_744': 744,
    
    # Ramanujan tau function
    'tau_691': 691,  # Appears in tau function
    'tau_24': 24,    # Ramanujan's constant
    
    # Moonshine
    'moonshine_196883': 196883,  # 196884 - 1
    'moonshine_21493760': 21493760,  # Next coefficient
    
    # Rooster
    'rooster': 71,
    
    # BDI primes
    'bdi_primes': [3, 13, 17, 23, 43, 53, 63],
    
    # Dedekind eta
    'dedekind_24': 24,
    
    # Eisenstein series
    'eisenstein_240': 240,
    'eisenstein_504': 504,
    'eisenstein_480': 480,
    'eisenstein_264': 264,
    
    # Discriminant
    'discriminant_1728': 1728,
}

def search_parquet_for_magic(parquet_dir):
    """Search all parquet files for magic numbers"""
    import pyarrow.parquet as pq
    
    parquet_dir = Path(parquet_dir)
    results = defaultdict(list)
    
    print("🔍 Searching LMFDB parquet files for magic numbers...")
    
    for pq_file in parquet_dir.glob('*.parquet'):
        try:
            table = pq.read_table(pq_file)
            df = table.to_pandas()
            
            # Search each column for magic numbers
            for col in df.columns:
                for magic_name, magic_val in MAGIC_NUMBERS.items():
                    if isinstance(magic_val, list):
                        continue
                    
                    # Check if magic number appears
                    if df[col].dtype in ['int64', 'float64']:
                        matches = df[df[col] == magic_val]
                        if len(matches) > 0:
                            results[magic_name].append({
                                'file': pq_file.name,
                                'column': col,
                                'count': len(matches),
                                'value': magic_val
                            })
                    
                    # Check string columns
                    elif df[col].dtype == 'object':
                        str_matches = df[df[col].astype(str).str.contains(str(magic_val), na=False)]
                        if len(str_matches) > 0:
                            results[magic_name].append({
                                'file': pq_file.name,
                                'column': col,
                                'count': len(str_matches),
                                'value': magic_val
                            })
            
            print(f"  ✓ {pq_file.name}")
        except Exception as e:
            print(f"  ✗ {pq_file.name}: {e}")
    
    return results

def extract_j_invariants(parquet_dir):
    """Extract j-invariant values from LMFDB"""
    import pyarrow.parquet as pq
    
    parquet_dir = Path(parquet_dir)
    j_values = []
    
    print("\n🔮 Extracting j-invariants...")
    
    for pq_file in parquet_dir.glob('*elliptic*.parquet'):
        try:
            table = pq.read_table(pq_file)
            df = table.to_pandas()
            
            # Look for j-invariant columns
            j_cols = [c for c in df.columns if 'j' in c.lower() or 'invariant' in c.lower()]
            
            for col in j_cols:
                vals = df[col].dropna().unique()
                j_values.extend(vals)
                print(f"  Found {len(vals)} j-invariants in {pq_file.name}:{col}")
        except Exception as e:
            pass
    
    return j_values

def main():
    lmfdb_dir = Path.home() / 'experiments' / 'monster'
    
    if not lmfdb_dir.exists():
        print(f"✗ LMFDB directory not found: {lmfdb_dir}")
        return
    
    # Search for magic numbers
    results = search_parquet_for_magic(lmfdb_dir)
    
    print("\n" + "="*60)
    print("🎯 MAGIC NUMBERS FOUND IN LMFDB")
    print("="*60)
    
    if not results:
        print("No magic numbers found in parquet files")
    else:
        for magic_name, occurrences in sorted(results.items()):
            print(f"\n{magic_name.upper()}: {MAGIC_NUMBERS[magic_name]}")
            for occ in occurrences:
                print(f"  📁 {occ['file']}")
                print(f"     Column: {occ['column']}")
                print(f"     Count: {occ['count']}")
    
    # Extract j-invariants
    j_vals = extract_j_invariants(lmfdb_dir)
    
    if j_vals:
        print(f"\n🔮 J-INVARIANTS: Found {len(j_vals)} unique values")
        
        # Check for special j-invariants
        special_j = [0, 1728, 196884, 744]
        found_special = [j for j in j_vals if j in special_j]
        
        if found_special:
            print(f"  Special j-invariants found: {found_special}")
    
    # Save results
    output = {
        'magic_numbers': MAGIC_NUMBERS,
        'found': {k: v for k, v in results.items()},
        'j_invariants': {
            'count': len(j_vals),
            'sample': list(j_vals[:20]) if j_vals else []
        }
    }
    
    output_file = Path.home() / 'introspector' / 'lmfdb_magic_numbers.json'
    with open(output_file, 'w') as f:
        json.dump(output, f, indent=2)
    
    print(f"\n💾 Saved to {output_file}")

if __name__ == '__main__':
    main()
