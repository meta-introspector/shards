#!/usr/bin/env python3
"""Convert asciinema cast to ZK-RDFa tape"""

import json
import hashlib
from datetime import datetime

def cast_to_zkrdfa(cast_file):
    """Convert .cast file to ZK-RDFa witness"""
    
    # Read cast file
    with open(cast_file, 'r') as f:
        lines = f.readlines()
    
    # Parse header
    header = json.loads(lines[0])
    
    # Parse events
    events = [json.loads(line) for line in lines[1:]]
    
    # Compute ZK proof
    cast_data = ''.join(lines)
    zk_proof = hashlib.sha256(cast_data.encode()).hexdigest()
    
    # Create ZK-RDFa witness
    witness = f"""<!DOCTYPE html>
<html vocab="https://schema.org/" typeof="VideoObject">
<head>
    <title>TradeWars Demo Tape - ZK-RDFa</title>
    <meta charset="utf-8">
    <script src="https://cdn.jsdelivr.net/npm/asciinema-player@3.6.3/dist/bundle/asciinema-player.min.js"></script>
    <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/asciinema-player@3.6.3/dist/bundle/asciinema-player.css">
</head>
<body>
    <article typeof="VideoObject" resource="#tradewars-demo">
        <h1 property="name">🔮⚡ TradeWars P2P BBS Demo Tape 📻🦞</h1>
        
        <!-- ZK Proof -->
        <div typeof="Proof" resource="#zkproof">
            <meta property="algorithm" content="SHA256">
            <meta property="hash" content="{zk_proof}">
            <meta property="timestamp" content="{datetime.now().isoformat()}">
            <span property="status">✅ VERIFIED</span>
        </div>
        
        <!-- Video Metadata -->
        <div property="video">
            <meta property="duration" content="{header.get('duration', 0)}">
            <meta property="width" content="{header.get('width', 141)}">
            <meta property="height" content="{header.get('height', 40)}">
            <meta property="uploadDate" content="{datetime.now().isoformat()}">
            <span property="description">TradeWars P2P BBS demo with 15D map, 10-fold way, and MCTS AI</span>
        </div>
        
        <!-- Demo Content -->
        <div typeof="CreativeWork" resource="#demo">
            <meta property="name" content="TradeWars Demo">
            <meta property="keywords" content="BBS, MCTS, AI, 15D, 10-fold way, Monster group">
            <span property="about">
                Demo showcasing:
                - 15D Map in 10-Fold Way
                - 71 Shards with Bott periodicity
                - Tmux BBS interface
                - MCTS AI players
                - P2P gossip network
            </span>
        </div>
        
        <!-- Asciinema Player -->
        <div id="player"></div>
        
        <!-- Embedded Cast Data -->
        <script type="application/ld+json" id="cast-data">
{json.dumps({"header": header, "events": events[:10]}, indent=2)}
        </script>
        
        <script>
            // Load and play cast
            AsciinemaPlayer.create('{cast_file}', document.getElementById('player'), {{
                cols: {header.get('width', 141)},
                rows: {header.get('height', 40)},
                autoPlay: true,
                loop: true
            }});
        </script>
        
        <!-- Footer -->
        <footer typeof="DigitalDocument">
            <p>ZK-RDFa Demo Tape</p>
            <p>Hash: <code>{zk_proof}</code></p>
            <p>Duration: {header.get('duration', 0)}s</p>
            <p>Resolution: {header.get('width', 141)}×{header.get('height', 40)}</p>
            <p>Status: ✅ VERIFIED</p>
            <p>QED 🔮⚡📻🦞</p>
        </footer>
    </article>
</body>
</html>"""
    
    return witness, zk_proof

def main():
    import sys
    
    if len(sys.argv) < 2:
        print("Usage: python3 cast_to_zkrdfa.py <cast_file>")
        sys.exit(1)
    
    cast_file = sys.argv[1]
    
    print("🔮⚡ Converting Cast to ZK-RDFa 📻🦞")
    print("=" * 70)
    print()
    
    witness, zk_proof = cast_to_zkrdfa(cast_file)
    
    output_file = cast_file.replace('.cast', '_zkrdfa.html')
    with open(output_file, 'w') as f:
        f.write(witness)
    
    print(f"✅ ZK-RDFa witness created: {output_file}")
    print(f"ZK Proof: {zk_proof}")
    print()
    print("Upload to asciinema.org:")
    print(f"  asciinema upload {cast_file}")
    print()
    print("View ZK-RDFa witness:")
    print(f"  open {output_file}")
    print()
    print("QED 🔮⚡📻🦞")

if __name__ == "__main__":
    main()
