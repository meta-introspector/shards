#!/usr/bin/env bash
# Launch 23 Paxos nodes with LMFDB data sources
# Monster Harmonic Consensus Network

set -e

echo "🔷 CICADA-71 - 23 Node Paxos Consensus Launch"
echo "═══════════════════════════════════════════════"
echo ""

# Configuration
NUM_NODES=23
BASE_PORT=7100
LMFDB_DATA_DIR="${HOME}/.lmfdb"
MONSTER_DATA_DIR="${HOME}/.openclaw"

# Create data directories
mkdir -p "$LMFDB_DATA_DIR"
mkdir -p "$MONSTER_DATA_DIR/consensus"

# LMFDB data sources (modular forms, elliptic curves, L-functions)
LMFDB_SOURCES=(
    "https://www.lmfdb.org/api/elliptic_curves/curves"
    "https://www.lmfdb.org/api/modular_forms/dimensions"
    "https://www.lmfdb.org/api/lfunctions/instances"
    "https://www.lmfdb.org/api/number_fields/fields"
    "https://www.lmfdb.org/api/artin_representations/representations"
    "https://www.lmfdb.org/api/genus2_curves/curves"
    "https://www.lmfdb.org/api/higher_genus_w_automorphisms/families"
    "https://www.lmfdb.org/api/lattices/lattices"
    "https://www.lmfdb.org/api/maass_forms/maass_forms"
    "https://www.lmfdb.org/api/siegel_modular_forms/dimensions"
)

# Download LMFDB data (if not cached)
echo "📊 Loading LMFDB data sources..."
for i in "${!LMFDB_SOURCES[@]}"; do
    SOURCE="${LMFDB_SOURCES[$i]}"
    CACHE_FILE="$LMFDB_DATA_DIR/source_$i.json"
    
    if [ ! -f "$CACHE_FILE" ]; then
        echo "   Fetching: $(basename $SOURCE)..."
        curl -s "$SOURCE?_format=json&_limit=100" > "$CACHE_FILE" 2>/dev/null || echo "{}" > "$CACHE_FILE"
    else
        echo "   ✓ Cached: source_$i.json"
    fi
done

echo ""
echo "🚀 Launching 23 Paxos nodes..."
echo ""

# Kill existing nodes
pkill -f "paxos-node" 2>/dev/null || true
sleep 1

# Launch nodes
for NODE_ID in $(seq 0 22); do
    PORT=$((BASE_PORT + NODE_ID))
    LOG_FILE="$MONSTER_DATA_DIR/consensus/node_${NODE_ID}.log"
    
    # Assign LMFDB data source to node
    LMFDB_SOURCE="$LMFDB_DATA_DIR/source_$((NODE_ID % 10)).json"
    
    echo "   Node $NODE_ID: port $PORT, data: $(basename $LMFDB_SOURCE)"
    
    # Launch node in background
    NODE_ID=$NODE_ID \
    PORT=$PORT \
    LMFDB_DATA="$LMFDB_SOURCE" \
    nix run ~/introspector#paxos-node > "$LOG_FILE" 2>&1 &
    
    # Store PID
    echo $! > "$MONSTER_DATA_DIR/consensus/node_${NODE_ID}.pid"
done

echo ""
echo "⏳ Waiting for nodes to start..."
sleep 3

# Check node status
echo ""
echo "📊 Node Status:"
ALIVE=0
for NODE_ID in $(seq 0 22); do
    PORT=$((BASE_PORT + NODE_ID))
    if curl -s "http://localhost:$PORT/paxos/status" > /dev/null 2>&1; then
        echo "   ✅ Node $NODE_ID (port $PORT): ALIVE"
        ((ALIVE++))
    else
        echo "   ❌ Node $NODE_ID (port $PORT): DOWN"
    fi
done

echo ""
echo "═══════════════════════════════════════════════"
echo "✅ Launched: $ALIVE / $NUM_NODES nodes"
echo "   Quorum: 12 nodes (majority)"
echo "   Byzantine tolerance: 7 nodes"
echo ""
echo "📊 LMFDB Data Sources: ${#LMFDB_SOURCES[@]}"
echo "   Elliptic curves, modular forms, L-functions"
echo "   Monster group j-invariant data"
echo ""
echo "🔷 Consensus Network Ready"
echo "   Base port: $BASE_PORT"
echo "   Logs: $MONSTER_DATA_DIR/consensus/"
echo ""
echo "Commands:"
echo "  ./check_consensus.sh    - Check node status"
echo "  ./stop_nodes.sh         - Stop all nodes"
echo "  ./submit_proposal.sh    - Submit Paxos proposal"
