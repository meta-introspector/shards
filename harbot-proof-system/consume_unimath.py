#!/usr/bin/env python3
"""
Consume Vlad's UniMath lang_model.v and map to Monster mycelium path 232 ↔ 323
"""

import json
import subprocess
import hashlib
from pathlib import Path
from typing import List, Dict, Any

# Monster mycelium path 232 ↔ 323
MYCELIUM_PATH = {
    'source': 232,
    'target': 323,
    'prime_support': ([8, 29], [17, 19]),  # 2³, 29 | 17, 19
    'shadow_parity': -1,                    # Shadow transition
    'framing_residue': 8                    # 2³ conserved
}

def read_coq_file(path: Path) -> str:
    """Read Coq file"""
    return path.read_text()

def extract_coq_definitions(coq_content: str) -> List[str]:
    """Extract Coq definitions"""
    defs = []
    for line in coq_content.split('\n'):
        if line.strip().startswith(('Definition', 'Theorem', 'Lemma', 'Inductive')):
            defs.append(line.strip())
    return defs

def coq_to_ocaml(coq_file: Path) -> str:
    """Extract OCaml from Coq (via coqc -extraction)"""
    try:
        result = subprocess.run(
            ['coqc', '-extraction', str(coq_file)],
            capture_output=True, text=True, timeout=10
        )
        return result.stdout
    except:
        return ""

def hash_to_monster_shard(data: str) -> int:
    """Map data to Monster shard (0-70)"""
    h = hashlib.sha256(data.encode()).digest()
    return int.from_bytes(h[:4], 'big') % 71

def map_to_mycelium_path(data: str, data_type: str) -> Dict[str, Any]:
    """Map data to mycelium path coordinate"""
    shard = hash_to_monster_shard(data)
    
    # Determine which side of path (232 or 323)
    if shard < 36:
        side = 'source'
        node = 232
        primes = MYCELIUM_PATH['prime_support'][0]
    else:
        side = 'target'
        node = 323
        primes = MYCELIUM_PATH['prime_support'][1]
    
    return {
        'data_type': data_type,
        'shard': shard,
        'side': side,
        'node': node,
        'active_primes': primes,
        'shadow_parity': MYCELIUM_PATH['shadow_parity'],
        'framing_residue': MYCELIUM_PATH['framing_residue'],
        'j_invariant': 744 + 196884 * shard
    }

def main():
    print("╔════════════════════════════════════════════════════════════╗")
    print("║     CONSUME UNIMATH → MONSTER MYCELIUM PATH 232 ↔ 323     ║")
    print("╚════════════════════════════════════════════════════════════╝\n")
    
    # Locate files
    lang_model_path = Path("/home/mdupont/test2/lang_agent/lib/lang_model.v")
    extract_path = Path("/home/mdupont/test2/lang_agent/lib/extract_lang_model.v")
    
    mappings = []
    
    # 1. Process Coq files
    if lang_model_path.exists():
        print(f"Processing {lang_model_path}...")
        coq_content = read_coq_file(lang_model_path)
        defs = extract_coq_definitions(coq_content)
        
        for i, defn in enumerate(defs[:20]):  # First 20 definitions
            mapping = map_to_mycelium_path(defn, 'coq_definition')
            mappings.append(mapping)
            print(f"  Def {i}: Shard {mapping['shard']} → {mapping['side']} ({mapping['node']})")
    
    # 2. Extract OCaml
    if lang_model_path.exists():
        print(f"\nExtracting OCaml from {lang_model_path}...")
        ocaml_code = coq_to_ocaml(lang_model_path)
        if ocaml_code:
            mapping = map_to_mycelium_path(ocaml_code, 'ocaml_extraction')
            mappings.append(mapping)
            print(f"  OCaml: Shard {mapping['shard']} → {mapping['side']} ({mapping['node']})")
    
    # 3. Process extract file
    if extract_path.exists():
        print(f"\nProcessing {extract_path}...")
        extract_content = read_coq_file(extract_path)
        mapping = map_to_mycelium_path(extract_content, 'coq_extract')
        mappings.append(mapping)
        print(f"  Extract: Shard {mapping['shard']} → {mapping['side']} ({mapping['node']})")
    
    # 4. Generate JSON witness
    witness = {
        'mycelium_path': MYCELIUM_PATH,
        'mappings': mappings,
        'statistics': {
            'total_mappings': len(mappings),
            'source_side': sum(1 for m in mappings if m['side'] == 'source'),
            'target_side': sum(1 for m in mappings if m['side'] == 'target'),
            'unique_shards': len(set(m['shard'] for m in mappings))
        }
    }
    
    output_path = Path('complete_proofs/unimath_monster_mapping.json')
    output_path.parent.mkdir(exist_ok=True)
    output_path.write_text(json.dumps(witness, indent=2))
    
    print("\n╔════════════════════════════════════════════════════════════╗")
    print("║     MAPPING COMPLETE                                       ║")
    print("╚════════════════════════════════════════════════════════════╝\n")
    
    print(f"Total mappings: {witness['statistics']['total_mappings']}")
    print(f"Source side (232): {witness['statistics']['source_side']}")
    print(f"Target side (323): {witness['statistics']['target_side']}")
    print(f"Unique shards: {witness['statistics']['unique_shards']}")
    print(f"\n✓ Witness saved: {output_path}")
    print("\nQED 🔮⚡📻🦞")

if __name__ == '__main__':
    main()
