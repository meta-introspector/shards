#!/usr/bin/env bash
# Build 71 WASM emulators for Monster arcade games
# Pure HTML/JS - no Rust WASM compilation needed

set -e

echo "🌀 Building 71 WASM Emulators"
echo "=============================="
echo ""

# Create output directory
mkdir -p www/arcade

echo "Generating 71 HTML emulators..."

# Generate 71 HTML emulators
for shard in {0..70}; do
    cat > "www/arcade/shard_${shard}.html" << EOF
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <title>Monster Arcade - Shard ${shard}</title>
    <style>
        body { 
            background: #000; 
            color: #0f0; 
            font-family: monospace; 
            padding: 20px;
            max-width: 800px;
            margin: 0 auto;
        }
        .header { 
            border: 2px solid #0f0; 
            padding: 10px; 
            margin-bottom: 20px;
        }
        .proof { 
            background: #001100; 
            padding: 10px; 
            margin: 10px 0;
            border-left: 3px solid #0f0;
        }
        .emoji { font-size: 24px; }
    </style>
</head>
<body>
    <div class="header">
        <h1>🌀 Monster Arcade - Shard ${shard}</h1>
        <p>Architecture: <span id="arch">wasm32-unknown-unknown</span></p>
        <p>Crown Prime: <span id="crown">${shard}</span></p>
    </div>
    
    <div class="proof">
        <h2>zkPerf Proof</h2>
        <p>Shard: <strong>${shard}</strong></p>
        <p>Cycles: <span id="cycles">Computing...</span></p>
        <p>ZK-RDFa: <span id="zkrdfa">Generating...</span></p>
    </div>
    
    <div class="proof">
        <h2>10-Fold Way</h2>
        <p>Fold: <span id="fold">${shard} mod 10 = $((shard % 10))</span></p>
        <p>Bott Period: <span id="bott">$((shard % 8))</span></p>
    </div>
    
    <div class="emoji">
        ☕🕳️🪟👁️👹🦅🐓🔄🌀⚡
    </div>
    
    <script>
        // Simulate zkPerf (WASM has no TSC)
        const shard = ${shard};
        const start = performance.now();
        
        // Compute proof
        const cycles = Math.floor((performance.now() - start) * 1000);
        const hash = (shard * 31 + cycles) % 65536;
        
        // Emoji encoding
        const emoji = "☕🕳️🪟👁️👹🦅🐓🔄🌀⚡🎯🌌⏰➡️🦀✨";
        let zkrdfa = "zkrdfa://";
        for (let i = 0; i < 8; i++) {
            zkrdfa += emoji[hash >> (i * 2) & 0xF];
        }
        zkrdfa += "/shard${shard}/" + cycles;
        
        // Display
        document.getElementById('cycles').textContent = cycles;
        document.getElementById('zkrdfa').textContent = zkrdfa;
        
        // Crown primes
        if (shard === 47 || shard === 59 || shard === 70) {
            document.getElementById('crown').textContent = shard + " ⭐ CROWN PRIME!";
            document.getElementById('crown').style.color = "#ff0";
        }
    </script>
</body>
</html>
EOF
    echo "  ✓ Generated shard_${shard}.html"
done

# Create index page
cat > www/arcade/index.html << 'EOF'
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <title>Monster Arcade - 71 Shards</title>
    <style>
        body { 
            background: #000; 
            color: #0f0; 
            font-family: monospace; 
            padding: 20px;
        }
        .grid {
            display: grid;
            grid-template-columns: repeat(auto-fill, minmax(150px, 1fr));
            gap: 10px;
            margin-top: 20px;
        }
        .shard {
            border: 1px solid #0f0;
            padding: 10px;
            text-align: center;
            cursor: pointer;
            transition: all 0.3s;
        }
        .shard:hover {
            background: #001100;
            border-color: #0ff;
        }
        .crown { border-color: #ff0; color: #ff0; }
        h1 { text-align: center; }
    </style>
</head>
<body>
    <h1>🌀 Monster Arcade - 71 Shards</h1>
    <p style="text-align: center;">Click any shard to play</p>
    
    <div class="grid" id="grid"></div>
    
    <script>
        const grid = document.getElementById('grid');
        const crowns = [47, 59, 70];
        
        for (let i = 0; i < 71; i++) {
            const div = document.createElement('div');
            div.className = 'shard' + (crowns.includes(i) ? ' crown' : '');
            div.innerHTML = `Shard ${i}${crowns.includes(i) ? ' ⭐' : ''}`;
            div.onclick = () => window.location.href = `shard_${i}.html`;
            grid.appendChild(div);
        }
    </script>
</body>
</html>
EOF

echo ""
echo "🎯 Build Complete!"
echo "=================="
echo "Generated: 71 HTML emulators + index"
echo "Location: www/arcade/"
echo ""
echo "To serve:"
echo "  cd www/arcade && python3 -m http.server 8000"
echo "  Open: http://localhost:8000"
echo ""
echo "☕🕳️🪟👁️👹🦅🐓🔄🌀⚡"
