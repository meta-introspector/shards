#!/usr/bin/env python3
"""
Gabulab Demo: Extract Monster Harmonics from Promptbook
"""

import json
import sys

# Example promptbook
EXAMPLE_BOOK = """
# CICADA-71 Door Game

-   PIPELINE URL `https://meta-introspector.github.io/shards/doorgame/cicada71.book.md`
-   INPUT PARAMETER `{playerName}` Name of the player
-   INPUT PARAMETER `{targetShard}` Shard number to visit (0-71)
-   OUTPUT PARAMETER `{shardResult}` Result of shard visit with ZK proof

## Visit Shard

-   PERSONA Jane, experienced cryptographer and ZK proof expert
-   EXPECT JSON

You are a CICADA-71 Door Game master.

## Generate ZK Proof

-   PERSONA Alice, zero-knowledge proof specialist
-   EXPECT JSON

Generate a zero-knowledge proof.

## Show Stats

-   PERSONA Bob, game statistician
-   EXPECT JSON

Show player statistics.
"""

MONSTER_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]
J_INVARIANT_COEFF = 196884
BOTT_PERIOD = 8
NUM_SHARDS = 71

def parse_promptbook(book):
    """Parse promptbook and extract topology"""
    nodes = []
    edges = []
    personas = []
    
    lines = book.strip().split('\n')
    node_id = 0
    
    for line in lines:
        line = line.strip()
        
        # Parse INPUT PARAMETER
        if 'INPUT PARAMETER' in line and '{' in line:
            param = line.split('{')[1].split('}')[0]
            nodes.append({
                'id': f'input_{node_id}',
                'type': 'input',
                'content': param
            })
            node_id += 1
        
        # Parse OUTPUT PARAMETER
        if 'OUTPUT PARAMETER' in line and '{' in line:
            param = line.split('{')[1].split('}')[0]
            nodes.append({
                'id': f'output_{node_id}',
                'type': 'output',
                'content': param
            })
            node_id += 1
        
        # Parse PERSONA
        if 'PERSONA' in line:
            desc = line.split('PERSONA')[1].strip()
            name = desc.split(',')[0].strip()
            personas.append({
                'name': name,
                'description': desc,
                'shard': len(personas) % NUM_SHARDS
            })
            nodes.append({
                'id': f'persona_{node_id}',
                'type': 'persona',
                'content': name
            })
            node_id += 1
        
        # Parse section headers
        if line.startswith('##'):
            nodes.append({
                'id': f'section_{node_id}',
                'type': 'section',
                'content': line
            })
            node_id += 1
    
    # Create edges (sequential flow)
    for i in range(len(nodes) - 1):
        edges.append({
            'from': nodes[i]['id'],
            'to': nodes[i + 1]['id'],
            'type': 'dataflow'
        })
    
    return {
        'nodes': nodes,
        'edges': edges,
        'personas': personas
    }

def shard_topology(topology):
    """Shard topology into 71 pieces"""
    shards = [{'nodes': [], 'edges': [], 'personas': []} for _ in range(NUM_SHARDS)]
    
    for i, node in enumerate(topology['nodes']):
        shard_idx = i % NUM_SHARDS
        shards[shard_idx]['nodes'].append(node)
    
    for i, edge in enumerate(topology['edges']):
        shard_idx = i % NUM_SHARDS
        shards[shard_idx]['edges'].append(edge)
    
    for i, persona in enumerate(topology['personas']):
        shard_idx = i % NUM_SHARDS
        shards[shard_idx]['personas'].append(persona)
    
    return shards

def extract_harmonics(book):
    """Extract Monster Harmonics from Promptbook"""
    topology = parse_promptbook(book)
    shards = shard_topology(topology)
    
    harmonics = []
    
    for i, shard in enumerate(shards):
        if not shard['nodes']:  # Skip empty shards
            continue
            
        prime = MONSTER_PRIMES[i % len(MONSTER_PRIMES)]
        j_inv = (i * 744) % J_INVARIANT_COEFF
        bott = i % BOTT_PERIOD
        
        harmonics.append({
            'shard': i,
            'prime': prime,
            'hecke_operator': f'T_{prime}',
            'j_invariant': j_inv,
            'bott_period': bott,
            'topology': shard
        })
    
    return harmonics

def visualize_harmonics(harmonics):
    """Visualize harmonics as ASCII art"""
    print("\n🔮⚡ GABULAB: MONSTER HARMONICS EXTRACTED 🔮⚡")
    print("=" * 70)
    print()
    
    for h in harmonics[:10]:  # Show first 10
        print(f"Shard {h['shard']:2d}: {h['hecke_operator']:5s} | j={h['j_invariant']:6d} | Bott={h['bott_period']} | Nodes={len(h['topology']['nodes'])}")
    
    if len(harmonics) > 10:
        print(f"... ({len(harmonics) - 10} more shards)")
    
    print()
    print(f"Total Harmonics: {len(harmonics)}")
    print(f"Monster Primes: {MONSTER_PRIMES}")
    print(f"j-invariant mod: {J_INVARIANT_COEFF}")
    print(f"Bott Period: {BOTT_PERIOD}")
    print()

def main():
    print("🔮⚡📖 Gabulab: The Yeast of Thought and Mind")
    print("=" * 70)
    print()
    
    # Use example book or read from file
    if len(sys.argv) > 1:
        with open(sys.argv[1], 'r') as f:
            book = f.read()
    else:
        book = EXAMPLE_BOOK
        print("Using example promptbook (cicada71.book.md)")
        print()
    
    # Extract harmonics
    harmonics = extract_harmonics(book)
    
    # Visualize
    visualize_harmonics(harmonics)
    
    # Save to JSON
    output_file = 'harmonics.json'
    with open(output_file, 'w') as f:
        json.dump(harmonics, f, indent=2)
    
    print(f"💾 Saved to {output_file}")
    print()
    print("🧬 The yeast has fermented thought into topology! 🍞")

if __name__ == '__main__':
    main()
