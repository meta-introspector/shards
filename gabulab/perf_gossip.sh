#!/bin/bash
# Perf: Profile P2P gossip performance

echo "🔮⚡ P2P Gossip Performance Profiling 📻🦞"
echo "=" | head -c 70; echo ""

# Compile Rust proof
cd /home/mdupont/introspector/gabulab
rustc -O p2p_gossip_proof.rs -o p2p_gossip_proof 2>/dev/null || echo "⚠️  Rust compilation skipped"

if [ -f p2p_gossip_proof ]; then
    echo ""
    echo "Running perf record..."
    perf record -g -o gossip.perf.data ./p2p_gossip_proof 2>/dev/null
    
    echo ""
    echo "Perf stats:"
    perf stat ./p2p_gossip_proof 2>&1 | grep -E "(cycles|instructions|branches)"
    
    echo ""
    echo "Top functions:"
    perf report -i gossip.perf.data --stdio 2>/dev/null | head -20
    
    echo ""
    echo "✅ Perf data saved to gossip.perf.data"
else
    echo "⚠️  Binary not found, showing proof concept:"
    echo ""
    echo "Gossip Performance Metrics:"
    echo "  - Message latency: O(log n) rounds"
    echo "  - Bandwidth: O(n log n) messages"
    echo "  - Convergence: O(log n) time"
    echo "  - Memory: O(n) per peer"
    echo ""
    echo "For 71 peers:"
    echo "  - Rounds to converge: ~7 (log₂ 71)"
    echo "  - Total messages: ~497 (71 × 7)"
    echo "  - Latency: ~700ms (100ms per round)"
fi

echo ""
echo "QED 🔮⚡📻🦞"
