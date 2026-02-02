#!/bin/bash
# Auto-record TradeWars demo (non-interactive)

OUTPUT="/home/mdupont/introspector/doorgame/tradewars_demo.cast"

echo "🔮⚡ Auto-Recording TradeWars Demo 📻🦞"
echo ""

# Create demo script
cat > /tmp/tradewars_auto_demo.sh << 'EOF'
#!/bin/bash

clear
echo "🔮⚡ TRADEWARS P2P BBS DEMO 📻🦞"
echo ""
sleep 1

echo "═══════════════════════════════════════════════════════════════════"
echo "DEMO 1: 15D Map in 10-Fold Way"
echo "═══════════════════════════════════════════════════════════════════"
sleep 2

python3 /home/mdupont/introspector/doorgame/map_15d_10fold.py
sleep 4

clear
echo ""
echo "═══════════════════════════════════════════════════════════════════"
echo "DEMO 2: Tmux BBS Interface"
echo "═══════════════════════════════════════════════════════════════════"
sleep 2

timeout 4 python3 /home/mdupont/introspector/doorgame/tmux_bbs.py 2>/dev/null || true
sleep 2

clear
echo ""
echo "🔮⚡ DEMO COMPLETE 📻🦞"
echo ""
echo "Features Demonstrated:"
echo "  ✅ 15D Map (71 shards)"
echo "  ✅ 10-Fold Way topology"
echo "  ✅ Bott periodicity (mod 8)"
echo "  ✅ Tmux BBS interface"
echo "  ✅ Player scores"
echo "  ✅ Monster harmonics"
echo "  ✅ P2P network status"
echo "  ✅ MCTS AI-Life"
echo ""
echo "QED 🔮⚡📻🦞"
sleep 2
EOF

chmod +x /tmp/tradewars_auto_demo.sh

# Record
echo "Recording to: $OUTPUT"
asciinema rec "$OUTPUT" -c "/tmp/tradewars_auto_demo.sh" --overwrite

echo ""
echo "✅ Recording complete: $OUTPUT"
echo ""

# Convert to ZK-RDFa
echo "Converting to ZK-RDFa..."
python3 /home/mdupont/introspector/doorgame/cast_to_zkrdfa.py "$OUTPUT"

echo ""
echo "QED 🔮⚡📻🦞"
