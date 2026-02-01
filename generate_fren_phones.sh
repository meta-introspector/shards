#!/usr/bin/env bash
# generate_fren_phones.sh - Generate phone numbers for all FRENs using 9 Muses
# Uses Hecke operator consensus to assign phone numbers

set -euo pipefail

WITNESS_DIR="witnesses/frens"
PHONE_DIR="witnesses/phones"
mkdir -p "$PHONE_DIR"

TOKENS=(
  "E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22"
  "BwUTq7fS6sfUmHDwAiCQZ3asSiPEapW5zDrsbwtapump"
  "GNBe3at5NDpu45z1foWwrVfdxYhFA5dYWqNm2JMVSCAM"
  "DD87KkJH3hJeTC8U3msdrbzwkApmjDrxXA3sTbC7FAKE"
  "9DgKaWyhitMG1AtAdAAozy9ZspRUa42omzrZHnHw5FUN"
  "Fuj6EDWQHBnQ3eEvYDujNQ4rPLSkhm3pBySbQ79Bpump"
  "9bzJn2jHQPCGsYKapFvytJQcbaz5FN2TtNB43jb1pump"
)

echo "📞 Generating FREN phone numbers via 9 Muses..."
echo "=================================================="

# Build 9 Muses if needed
if [ ! -f "shard0/9muses/result/bin/nine-muses" ]; then
  echo "Building 9 Muses with Nix..."
  cd shard0/9muses && nix build && cd ../..
fi

for i in "${!TOKENS[@]}"; do
  TOKEN="${TOKENS[$i]}"
  NUM=$((i + 1))
  SHARD=$((0x$(echo -n "$TOKEN" | sha256sum | cut -c1-2) % 71))
  
  echo "[$NUM/7] $TOKEN (Shard $SHARD)"
  
  PHONE_FILE="$PHONE_DIR/${TOKEN}_phone.json"
  
  # Run 9 Muses consensus
  if [ -f "shard0/9muses/result/bin/nine-muses" ]; then
    OUTPUT=$(./shard0/9muses/result/bin/nine-muses "$TOKEN" 2>&1 || echo "failed")
    PHONE=$(echo "$OUTPUT" | grep "Best phone number:" | cut -d: -f2 | xargs || echo "+1-000-000-0000")
    SCORE=$(echo "$OUTPUT" | grep "Consensus score:" | grep -oP '\d+\.\d+' || echo "0.0")
    QUORUM=$(echo "$OUTPUT" | grep -q "QUORUM REACHED" && echo "true" || echo "false")
  else
    # Fallback: hash-based phone
    HASH=$(echo -n "$TOKEN" | sha256sum | cut -d' ' -f1)
    D1=${HASH:0:3}
    D2=${HASH:3:3}
    D3=${HASH:6:4}
    PHONE="+1-$((0x$D1 % 1000))-$((0x$D2 % 1000))-$((0x$D3 % 10000))"
    SCORE="0.5"
    QUORUM="false"
  fi
  
  mkdir -p "$PHONE_DIR"
  cat > "$PHONE_FILE" <<EOF
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "token": "$TOKEN",
  "shard": $SHARD,
  "phone": "$PHONE",
  "consensus": {
    "score": $SCORE,
    "quorum": $QUORUM,
    "method": "9_muses_hecke_operator"
  }
}
EOF
  
  echo "   📞 $PHONE (score: $SCORE, quorum: $QUORUM)"
  echo ""
done

echo "=================================================="
echo "✨ Phone numbers generated!"
echo ""
echo "FREN Directory:"
for PHONE_FILE in "$PHONE_DIR"/*.json; do
  TOKEN=$(jq -r .token "$PHONE_FILE")
  PHONE=$(jq -r .phone "$PHONE_FILE")
  SHARD=$(jq -r .shard "$PHONE_FILE")
  echo "  $PHONE → $TOKEN (Shard $SHARD)"
done
echo ""
echo "Total: $(ls -1 "$PHONE_DIR"/*.json 2>/dev/null | wc -l) FRENs"
