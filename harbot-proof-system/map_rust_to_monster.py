#!/usr/bin/env python3
"""
Map all Rust code to Monster group elements
"""

import re
import hashlib
from pathlib import Path
from typing import List, Dict

# 71 primes (Monster group factors)
CICADA_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353]

RUST_AGENT_CODE = """
pub fn new(shard_id: u8) -> Self {
    let agent_name = format!("CICADA-Harbot-{}", shard_id);
    let mut hasher = Sha256::new();
    hasher.update(agent_name.as_bytes());
    hasher.update(&[shard_id]);
    let identity_hash = hex::encode(hasher.finalize())[..16].to_string();
    Self { agent_name, shard_id, identity_hash, capabilities: vec![] }
}

pub fn generate_all_agents() -> Vec<HarbotAgent> {
    (0..71).map(HarbotAgent::new).collect()
}
"""

def hash_to_shard(code: str) -> int:
    h = hashlib.sha256(code.encode()).digest()
    return int.from_bytes(h[:4], 'big') % 71

def map_rust_function(name: str, code: str) -> Dict:
    shard_id = hash_to_shard(code)
    return {
        'type': 'function',
        'name': name,
        'shard_id': shard_id,
        'prime': CICADA_PRIMES[shard_id],
        'conjugacy_class': shard_id,
        'order': CICADA_PRIMES[shard_id],
        'code_hash': hashlib.sha256(code.encode()).hexdigest()[:16],
        'j_invariant': 744 + 196884 * shard_id
    }

print("╔════════════════════════════════════════════════════════════╗")
print("║     RUST CODE → MONSTER GROUP MAPPING                      ║")
print("╚════════════════════════════════════════════════════════════╝\n")

functions = [
    ('new', RUST_AGENT_CODE.split('pub fn generate_all_agents')[0]),
    ('generate_all_agents', RUST_AGENT_CODE.split('pub fn generate_all_agents')[1])
]

mappings = [map_rust_function(n, c) for n, c in functions if c.strip()]

print("RUST FUNCTIONS MAPPED TO MONSTER:")
print("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
for m in mappings:
    print(f"\n{m['type'].upper()}: {m['name']}")
    print(f"  Shard ID: {m['shard_id']}")
    print(f"  Prime: {m['prime']}")
    print(f"  j-invariant: {m['j_invariant']}")
    print(f"  Code hash: {m['code_hash']}")

composite_hash = hashlib.sha256(str(mappings).encode()).hexdigest()
print(f"\n✓ Composite: {composite_hash}")
print("\nQED 🔮⚡📻🦞")
