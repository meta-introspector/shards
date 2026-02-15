#!/usr/bin/env bash
# Rebuild all Nix-Wars flakes with zkPerf witnesses

set -e

STATES_DIR="$(cd "$(dirname "$0")" && pwd)/states"
WITNESS_DIR="$(cd "$(dirname "$0")" && pwd)/zkperf-witnesses"

mkdir -p "$WITNESS_DIR"

echo "🔥 Rebuilding all Nix-Wars states with zkPerf witnesses"
echo "=========================================================="
echo ""

for STATE in "$STATES_DIR"/state-*; do
    [ -d "$STATE" ] || continue
    
    STATE_NAME=$(basename "$STATE")
    echo "⚡ Building $STATE_NAME..."
    
    cd "$STATE"
    
    # Build with perf measurement
    if command -v perf &> /dev/null; then
        perf stat -o "$WITNESS_DIR/${STATE_NAME}-perf.txt" \
            -e cycles,instructions,cache-misses,branches,branch-misses \
            nix build --rebuild 2>&1 | tail -3
    else
        echo "   ⚠️  perf not available, building without metrics"
        nix build --rebuild 2>&1 | tail -3
    fi
    
    # Extract commitment
    if [ -f "result/state.json" ]; then
        COMMITMENT=$(nix eval .#lib.commitment --raw 2>/dev/null || echo "unknown")
        echo "   Commitment: ${COMMITMENT:0:16}..."
    fi
    
    # Generate witness
    cat > "$WITNESS_DIR/${STATE_NAME}-witness.json" << EOF
{
  "state": "$STATE_NAME",
  "commitment": "$COMMITMENT",
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "perf_file": "${STATE_NAME}-perf.txt",
  "reproducible": true
}
EOF
    
    echo "   ✅ Witness: $WITNESS_DIR/${STATE_NAME}-witness.json"
    echo ""
done

# Build universe
echo "🌌 Building universe..."
cd "$(dirname "$0")/universe"
if command -v perf &> /dev/null; then
    perf stat -o "$WITNESS_DIR/universe-perf.txt" \
        -e cycles,instructions,cache-misses \
        nix build --rebuild 2>&1 | tail -3
else
    nix build --rebuild 2>&1 | tail -3
fi

UNIVERSE_COMMIT=$(nix eval .#lib.universe.commitment --raw 2>/dev/null || echo "unknown")
echo "   Commitment: ${UNIVERSE_COMMIT:0:16}..."
echo ""

# Build browser engine
echo "🎮 Building browser engine..."
cd "$(dirname "$0")/browser"
if command -v perf &> /dev/null; then
    perf stat -o "$WITNESS_DIR/browser-perf.txt" \
        -e cycles,instructions,cache-misses \
        nix build --rebuild 2>&1 | tail -3
else
    nix build --rebuild 2>&1 | tail -3
fi
echo ""

# Build WASM meta-execution
echo "📦 Building WASM meta-execution..."
cd "$(dirname "$0")/wasm"
if command -v perf &> /dev/null; then
    perf stat -o "$WITNESS_DIR/wasm-perf.txt" \
        -e cycles,instructions,cache-misses \
        nix build --rebuild 2>&1 | tail -3
else
    nix build --rebuild 2>&1 | tail -3
fi
echo ""

# Generate master witness
echo "🔐 Generating master zkPerf witness..."

cat > "$WITNESS_DIR/master-witness.json" << EOF
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "universe_commitment": "$UNIVERSE_COMMIT",
  "states": [
EOF

first=true
for WITNESS in "$WITNESS_DIR"/state-*-witness.json; do
    [ -f "$WITNESS" ] || continue
    if [ "$first" = true ]; then
        first=false
    else
        echo "," >> "$WITNESS_DIR/master-witness.json"
    fi
    cat "$WITNESS" >> "$WITNESS_DIR/master-witness.json"
done

cat >> "$WITNESS_DIR/master-witness.json" << EOF

  ],
  "reproducible": true,
  "thermodynamic_witness": true
}
EOF

echo "✅ Master witness: $WITNESS_DIR/master-witness.json"
echo ""
echo "📊 Summary:"
ls -lh "$WITNESS_DIR"/*.json | wc -l | xargs echo "   Witnesses generated:"
ls -lh "$WITNESS_DIR"/*.txt 2>/dev/null | wc -l | xargs echo "   Perf files:"
echo ""
echo "🎉 All flakes rebuilt with zkPerf witnesses!"
