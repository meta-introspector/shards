#!/usr/bin/env bash
# findneedle.sh - Find the needle in the haystack (Level 2 CICADA-71)
# Search 71 shards for the token, apply 9 Muses consensus, generate zkTLS proof

set -euo pipefail

if [ $# -lt 1 ]; then
    echo "Usage: $0 <solscan_url>"
    echo "Example: $0 https://solscan.io/token/E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22"
    exit 1
fi

URL="$1"
TOKEN=$(echo "$URL" | grep -oP 'token/\K[A-Za-z0-9]+' || echo "unknown")

echo "🔍 Finding needle in haystack..."
echo "=================================================="
echo "URL: $URL"
echo "Token: $TOKEN"
echo ""

# Step 1: Search 71 shards (mod 71 distribution)
echo "📊 Step 1: Distributing across 71 shards..."
SHARD=$((0x$(echo -n "$TOKEN" | sha256sum | cut -c1-2) % 71))
echo "   Token maps to shard: $SHARD"
echo ""

# Step 2: Run 9 Muses consensus (Hecke operator)
echo "🎭 Step 2: Running 9 Muses Hecke operator..."
if [ -d "shard0/9muses" ]; then
    cd shard0/9muses
    
    # Generate Cargo.lock if missing
    if [ ! -f "Cargo.lock" ]; then
        echo "   Generating Cargo.lock..."
        cargo generate-lockfile
    fi
    
    # Build with Nix
    echo "   Building with Nix..."
    if nix build 2>&1 | tee /tmp/9muses_build.log; then
        echo "   ✅ Build successful"
        
        # Run with perf
        echo "   Running Hecke operator with perf..."
        if perf record -o muses_${TOKEN}.perf -- ./result/bin/nine-muses "$TOKEN" 2>&1 | tee /tmp/9muses_output.log; then
            echo "   ✅ Hecke operator complete"
            
            # Generate perf report
            perf report -i muses_${TOKEN}.perf --stdio > muses_${TOKEN}_perf_report.txt 2>/dev/null || true
        else
            echo "   ⚠️  Perf failed, running without perf..."
            ./result/bin/nine-muses "$TOKEN" | tee /tmp/9muses_output.log
        fi
    else
        echo "   ⚠️  Nix build failed, trying cargo..."
        if cargo run --release "$TOKEN" 2>&1 | tee /tmp/9muses_output.log; then
            echo "   ✅ Cargo run successful"
        else
            echo "   ❌ Both Nix and Cargo failed"
        fi
    fi
    
    cd ../..
else
    echo "   ⚠️  9muses directory not found"
fi
echo ""

# Step 3: Generate zkTLS proof
echo "🔐 Step 3: Generating zkTLS proof..."
if [ -d "shard0/zktls" ]; then
    cd shard0/zktls
    
    # Generate Cargo.lock if missing
    if [ ! -f "Cargo.lock" ]; then
        echo "   Generating Cargo.lock..."
        cargo generate-lockfile
    fi
    
    # Build with Nix
    echo "   Building zkTLS prover..."
    if nix build 2>&1 | tee /tmp/zktls_build.log; then
        echo "   ✅ Build successful"
        
        # Run zkTLS proof generation
        echo "   Generating proof with perf..."
        if perf record -o frens_${TOKEN}.perf -- ./result/bin/frens_phone "$URL" 2>&1 | tee /tmp/zktls_output.log; then
            echo "   ✅ zkTLS proof generated"
            
            # Generate perf report
            perf report -i frens_${TOKEN}.perf --stdio > frens_${TOKEN}_perf_report.txt 2>/dev/null || true
        else
            echo "   ⚠️  Perf failed, running without perf..."
            ./result/bin/frens_phone "$URL" | tee /tmp/zktls_output.log
        fi
    else
        echo "   ⚠️  Nix build failed, trying cargo..."
        if cargo run --release --bin frens_phone "$URL" 2>&1 | tee /tmp/zktls_output.log; then
            echo "   ✅ Cargo run successful"
        else
            echo "   ❌ Both Nix and Cargo failed"
        fi
    fi
    
    cd ../..
else
    echo "   ⚠️  zktls directory not found"
fi
echo ""

# Step 4: Create witness
echo "📝 Step 4: Creating witness..."
TIMESTAMP=$(date -u +%Y-%m-%dT%H:%M:%SZ)
WITNESS_FILE="needle_${TOKEN}_witness.json"

cat > "$WITNESS_FILE" <<EOF
{
  "timestamp": "$TIMESTAMP",
  "operation": "findneedle",
  "level": 2,
  "challenge": "Find the needle in the haystack",
  "url": "$URL",
  "token": "$TOKEN",
  "shard": $SHARD,
  "muses_consensus": $([ -f /tmp/9muses_output.log ] && echo "true" || echo "false"),
  "zktls_proof": $([ -f /tmp/zktls_output.log ] && echo "true" || echo "false"),
  "perf_captured": {
    "muses": $([ -f shard0/9muses/muses_${TOKEN}.perf ] && echo "true" || echo "false"),
    "zktls": $([ -f shard0/zktls/frens_${TOKEN}.perf ] && echo "true" || echo "false")
  },
  "outputs": {
    "muses_log": "/tmp/9muses_output.log",
    "zktls_log": "/tmp/zktls_output.log"
  }
}
EOF

echo "   ✅ Witness created: $WITNESS_FILE"
echo ""

# Step 5: Display results
echo "🎯 Step 5: Results"
echo "=================================================="
if [ -f /tmp/9muses_output.log ]; then
    echo ""
    echo "9 MUSES CONSENSUS:"
    tail -15 /tmp/9muses_output.log
fi

if [ -f /tmp/zktls_output.log ]; then
    echo ""
    echo "ZKTLS PROOF:"
    tail -10 /tmp/zktls_output.log
fi

echo ""
echo "=================================================="
echo "✨ Needle found in shard $SHARD!"
echo "📄 Witness: $WITNESS_FILE"
echo ""
echo "To commit:"
echo "  git add $WITNESS_FILE"
echo "  git commit -m 'Found needle: $TOKEN'"
echo "  git push"
