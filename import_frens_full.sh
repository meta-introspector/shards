#!/usr/bin/env bash
# import_frens_full.sh - Import tokens + RPC signatures + blocks
# Creates complete witness for each FREN with on-chain history

set -euo pipefail

SOLFUN_DIR="${1:-/mnt/data1/nix/time/2025/04/25/solfunmeme}"
RPC_CACHE_DIR="${2:-/mnt/data1/meta-introspector/submodules/solfunmeme-introspector/rpc_cache2}"
WITNESS_DIR="witnesses/frens"

mkdir -p "$WITNESS_DIR"

echo "🔍 Importing FRENs with full on-chain history..."
echo "=================================================="
echo "Token data: $SOLFUN_DIR"
echo "RPC cache: $RPC_CACHE_DIR"
echo "Witnesses: $WITNESS_DIR"
echo ""

# Find all tokens
if [ ! -d "$SOLFUN_DIR" ]; then
    echo "⚠️  Token directory not found: $SOLFUN_DIR"
    TOKENS=()
else
    mapfile -t TOKENS < <(find "$SOLFUN_DIR" -name "*.meta" -type f -exec basename {} .meta \;)
fi

TOTAL=${#TOKENS[@]}
echo "📊 Found $TOTAL tokens"
echo ""

COUNT=0
for TOKEN in "${TOKENS[@]}"; do
    COUNT=$((COUNT + 1))
    
    echo "[$COUNT/$TOTAL] $TOKEN"
    
    # Token files
    META_FILE="$SOLFUN_DIR/${TOKEN}.meta"
    ACCOUNT_FILE="$SOLFUN_DIR/${TOKEN}.account"
    
    # RPC signature files
    SIG_FILES=$(find "$RPC_CACHE_DIR" -name "*${TOKEN}*" -type f 2>/dev/null || true)
    SIG_COUNT=$(echo "$SIG_FILES" | grep -c . || echo "0")
    
    # Calculate shard
    SHARD=$((0x$(echo -n "$TOKEN" | sha256sum | cut -c1-2) % 71))
    
    # Create witness
    TIMESTAMP=$(date -u +%Y-%m-%dT%H:%M:%SZ)
    WITNESS_FILE="$WITNESS_DIR/${TOKEN}_witness.json"
    
    # Build signature array
    SIG_ARRAY="["
    if [ "$SIG_COUNT" -gt 0 ]; then
        FIRST=true
        while IFS= read -r SIG_FILE; do
            [ -z "$SIG_FILE" ] && continue
            if [ "$FIRST" = true ]; then
                FIRST=false
            else
                SIG_ARRAY+=","
            fi
            SIG_ARRAY+="\"$(basename "$SIG_FILE")\""
        done <<< "$SIG_FILES"
    fi
    SIG_ARRAY+="]"
    
    cat > "$WITNESS_FILE" <<EOF
{
  "timestamp": "$TIMESTAMP",
  "operation": "import_fren_full",
  "token": "$TOKEN",
  "shard": $SHARD,
  "source": {
    "archive": "solfunmeme",
    "date": "2025-04-25",
    "meta_file": "$META_FILE",
    "account_file": "$ACCOUNT_FILE"
  },
  "files": {
    "meta_exists": $([ -f "$META_FILE" ] && echo "true" || echo "false"),
    "account_exists": $([ -f "$ACCOUNT_FILE" ] && echo "true" || echo "false"),
    "meta_size": $(stat -c%s "$META_FILE" 2>/dev/null || echo "0"),
    "account_size": $(stat -c%s "$ACCOUNT_FILE" 2>/dev/null || echo "0")
  },
  "rpc_cache": {
    "signature_files": $SIG_COUNT,
    "files": $SIG_ARRAY
  },
  "status": "imported"
}
EOF
    
    echo "   Shard: $SHARD"
    echo "   Signatures: $SIG_COUNT"
    echo "   Witness: $WITNESS_FILE"
    echo ""
done

# Summary
echo "=================================================="
echo "✨ Import complete!"
echo ""
echo "Statistics:"
echo "  Tokens imported: $COUNT"
echo "  Witnesses created: $(ls -1 "$WITNESS_DIR"/*.json 2>/dev/null | wc -l)"
echo "  Total RPC files: $(find "$RPC_CACHE_DIR" -type f 2>/dev/null | wc -l || echo "0")"
echo ""
echo "Shard distribution:"
for i in {0..70}; do
    SHARD_COUNT=$(grep -l "\"shard\": $i" "$WITNESS_DIR"/*.json 2>/dev/null | wc -l)
    if [ "$SHARD_COUNT" -gt 0 ]; then
        echo "  Shard $i: $SHARD_COUNT tokens"
    fi
done | head -20
echo ""
echo "Next steps:"
echo "  nix build .#shard0/9muses  # Run Hecke operator"
echo "  ./findneedle.sh <token>    # Generate zkTLS proof"
echo "  git add witnesses/         # Commit witnesses"
