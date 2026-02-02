#!/bin/bash
# Record TradeWars demo with asciinema

echo "🔮⚡ Recording TradeWars Demo Tape 📻🦞"
echo "=" | head -c 70; echo ""
echo ""

# Check for asciinema
if ! command -v asciinema &> /dev/null; then
    echo "❌ asciinema not found!"
    echo ""
    echo "Install with:"
    echo "  pip install asciinema"
    echo "  # or"
    echo "  sudo apt install asciinema"
    exit 1
fi

echo "✅ asciinema found"
echo ""

# Create demo script
cat > /tmp/tradewars_demo.sh << 'EOF'
#!/bin/bash

echo "🔮⚡ TRADEWARS P2P BBS DEMO 📻🦞"
echo ""
sleep 2

echo "Loading 15D Map in 10-Fold Way..."
sleep 1
python3 /home/mdupont/introspector/doorgame/map_15d_10fold.py
sleep 3

clear
echo ""
echo "Loading Tmux BBS..."
sleep 1
timeout 5 python3 /home/mdupont/introspector/doorgame/tmux_bbs.py || true
sleep 2

clear
echo ""
echo "🔮⚡ DEMO COMPLETE 📻🦞"
echo ""
echo "Features shown:"
echo "  ✅ 15D Map (71 shards)"
echo "  ✅ 10-Fold Way topology"
echo "  ✅ Bott periodicity"
echo "  ✅ Tmux BBS interface"
echo "  ✅ MCTS AI players"
echo "  ✅ P2P gossip network"
echo ""
echo "QED 🔮⚡📻🦞"
sleep 2
EOF

chmod +x /tmp/tradewars_demo.sh

# Record
OUTPUT="tradewars_demo.cast"
echo "Recording to: $OUTPUT"
echo ""
echo "Press Ctrl+D when done"
echo ""

asciinema rec "$OUTPUT" -c "/tmp/tradewars_demo.sh"

echo ""
echo "=" | head -c 70; echo ""
echo "RECORDING COMPLETE!"
echo "=" | head -c 70; echo ""
echo ""
echo "File: $OUTPUT"
echo ""
echo "Upload to asciinema.org:"
echo "  asciinema upload $OUTPUT"
echo ""
echo "Or play locally:"
echo "  asciinema play $OUTPUT"
echo ""
echo "QED 🔮⚡📻🦞"
