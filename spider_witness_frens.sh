#!/usr/bin/env bash
# spider_witness_frens.sh - Spider and witness all FREN pages to depth N
# Uses wget spider with TLZ witnessing

set -euo pipefail

DEPTH="${1:-2}"
PAGES_DIR="witnesses/pages"
SPIDER_DIR="witnesses/spider"
mkdir -p "$SPIDER_DIR"

TOKENS=(
  "E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22"
  "BwUTq7fS6sfUmHDwAiCQZ3asSiPEapW5zDrsbwtapump"
  "GNBe3at5NDpu45z1foWwrVfdxYhFA5dYWqNm2JMVSCAM"
  "DD87KkJH3hJeTC8U3msdrbzwkApmjDrxXA3sTbC7FAKE"
  "9DgKaWyhitMG1AtAdAAozy9ZspRUa42omzrZHnHw5FUN"
  "Fuj6EDWQHBnQ3eEvYDujNQ4rPLSkhm3pBySbQ79Bpump"
  "9bzJn2jHQPCGsYKapFvytJQcbaz5FN2TtNB43jb1pump"
)

echo "🕷️  Spidering FREN pages to depth $DEPTH..."
echo "=================================================="

for i in "${!TOKENS[@]}"; do
  TOKEN="${TOKENS[$i]}"
  NUM=$((i + 1))
  SHARD=$((0x$(echo -n "$TOKEN" | sha256sum | cut -c1-2) % 71))
  
  echo "[$NUM/7] $TOKEN (Shard $SHARD)"
  
  TOKEN_DIR="$SPIDER_DIR/$TOKEN"
  mkdir -p "$TOKEN_DIR"
  
  # Spider solscan
  echo "   Spidering solscan.io depth $DEPTH..."
  wget --spider --recursive --level=$DEPTH --no-parent \
    --domains=solscan.io \
    --reject="*.jpg,*.jpeg,*.png,*.gif,*.svg,*.ico,*.woff,*.woff2,*.ttf" \
    --wait=1 --random-wait \
    -o "$TOKEN_DIR/solscan_spider.log" \
    "https://solscan.io/token/$TOKEN" 2>&1 || true
  
  # Spider pump.fun
  echo "   Spidering pump.fun depth $DEPTH..."
  wget --spider --recursive --level=$DEPTH --no-parent \
    --domains=pump.fun \
    --reject="*.jpg,*.jpeg,*.png,*.gif,*.svg,*.ico,*.woff,*.woff2,*.ttf" \
    --wait=1 --random-wait \
    -o "$TOKEN_DIR/pumpfun_spider.log" \
    "https://pump.fun/coin/$TOKEN" 2>&1 || true
  
  # Extract all URLs
  grep -oP 'https?://[^\s"<>]+' "$TOKEN_DIR"/*.log | sort -u > "$TOKEN_DIR/urls.txt" || true
  
  # Create TLZ witness
  TIMESTAMP=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  URL_COUNT=$(wc -l < "$TOKEN_DIR/urls.txt" 2>/dev/null || echo "0")
  
  cat > "$TOKEN_DIR/witness.json" <<EOF
{
  "timestamp": "$TIMESTAMP",
  "protocol": "TLZ/1.0",
  "token": "$TOKEN",
  "shard": $SHARD,
  "spider": {
    "depth": $DEPTH,
    "urls_discovered": $URL_COUNT,
    "domains": ["solscan.io", "pump.fun"]
  },
  "files": {
    "urls": "$TOKEN_DIR/urls.txt",
    "solscan_log": "$TOKEN_DIR/solscan_spider.log",
    "pumpfun_log": "$TOKEN_DIR/pumpfun_spider.log"
  }
}
EOF
  
  echo "   ✅ Discovered $URL_COUNT URLs"
  echo ""
done

echo "=================================================="
echo "✨ Spider complete!"
echo ""
echo "Summary:"
for TOKEN in "${TOKENS[@]}"; do
  WITNESS="$SPIDER_DIR/$TOKEN/witness.json"
  if [ -f "$WITNESS" ]; then
    URLS=$(jq -r .spider.urls_discovered "$WITNESS")
    echo "  $TOKEN: $URLS URLs"
  fi
done
