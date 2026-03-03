#!/usr/bin/env bash
# zkPerf witness for deployment verification

set -e

DEPLOYMENT_URL="${1:-http://solana.solfunmeme.com:8080}"
WITNESS_FILE="/tmp/deployment-witness-$(date +%s).json"

echo "⚡ zkPerf Deployment Witness"
echo "============================"
echo ""
echo "Target: $DEPLOYMENT_URL"
echo ""

# Measure deployment verification
START=$(date +%s%N)

# Test endpoints
echo "📡 Testing endpoints..."
ENDPOINTS=(
  "/"
  "/bbs.html"
  "/url-only.html"
  "/flying-fractran.html"
  "/nix-wars-orbits.json"
)

RESULTS=()
for endpoint in "${ENDPOINTS[@]}"; do
  URL="$DEPLOYMENT_URL$endpoint"
  
  # Measure with perf if available
  if command -v perf &> /dev/null; then
    perf stat -e cycles,instructions,cache-misses \
      -o "/tmp/perf-$endpoint.txt" \
      curl -s -o /dev/null -w "%{http_code}" "$URL" 2>&1 | tail -1
    STATUS=$?
  else
    STATUS=$(curl -s -o /dev/null -w "%{http_code}" "$URL")
  fi
  
  HASH=$(curl -s "$URL" | sha256sum | cut -d' ' -f1)
  SIZE=$(curl -s "$URL" | wc -c)
  
  RESULTS+=("{\"endpoint\":\"$endpoint\",\"status\":$STATUS,\"hash\":\"$HASH\",\"size\":$SIZE}")
  
  echo "  $endpoint: $STATUS (${SIZE} bytes, ${HASH:0:16}...)"
done

END=$(date +%s%N)
ELAPSED=$(( ($END - $START) / 1000000 ))

# Generate witness
cat > "$WITNESS_FILE" << EOF
{
  "deployment": {
    "url": "$DEPLOYMENT_URL",
    "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
    "elapsed_ms": $ELAPSED
  },
  "endpoints": [
    $(IFS=,; echo "${RESULTS[*]}")
  ],
  "system": {
    "hostname": "$(hostname)",
    "kernel": "$(uname -r)",
    "arch": "$(uname -m)"
  },
  "commitment": "$(echo "${RESULTS[*]}" | sha256sum | cut -d' ' -f1)",
  "reproducible": true
}
EOF

echo ""
echo "✅ Witness generated: $WITNESS_FILE"
echo ""
cat "$WITNESS_FILE" | jq . 2>/dev/null || cat "$WITNESS_FILE"
echo ""
echo "🔐 Deployment Commitment: $(jq -r .commitment "$WITNESS_FILE" 2>/dev/null | cut -c1-16)..."
