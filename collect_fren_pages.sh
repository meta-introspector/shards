#!/usr/bin/env bash
# collect_fren_pages.sh - Collect all FREN pages and linked content
# Fetches: token pages, home pages, linked pages

set -euo pipefail

PAGES_DIR="witnesses/pages"
mkdir -p "$PAGES_DIR"

TOKENS=(
  "E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22"
  "BwUTq7fS6sfUmHDwAiCQZ3asSiPEapW5zDrsbwtapump"
  "GNBe3at5NDpu45z1foWwrVfdxYhFA5dYWqNm2JMVSCAM"
  "DD87KkJH3hJeTC8U3msdrbzwkApmjDrxXA3sTbC7FAKE"
  "9DgKaWyhitMG1AtAdAAozy9ZspRUa42omzrZHnHw5FUN"
  "Fuj6EDWQHBnQ3eEvYDujNQ4rPLSkhm3pBySbQ79Bpump"
  "9bzJn2jHQPCGsYKapFvytJQcbaz5FN2TtNB43jb1pump"
)

echo "🌐 Collecting FREN pages..."
echo "=================================================="

for i in "${!TOKENS[@]}"; do
  TOKEN="${TOKENS[$i]}"
  NUM=$((i + 1))
  
  echo "[$NUM/7] $TOKEN"
  
  TOKEN_DIR="$PAGES_DIR/$TOKEN"
  mkdir -p "$TOKEN_DIR"
  
  # Fetch token page
  echo "   Fetching solscan..."
  curl -s "https://solscan.io/token/$TOKEN" > "$TOKEN_DIR/solscan.html" || true
  
  # Fetch pump.fun page
  echo "   Fetching pump.fun..."
  curl -s "https://pump.fun/coin/$TOKEN" > "$TOKEN_DIR/pumpfun.html" || true
  
  # Fetch home pages
  echo "   Fetching home pages..."
  curl -s "https://solscan.io" > "$TOKEN_DIR/solscan_home.html" || true
  curl -s "https://pump.fun" > "$TOKEN_DIR/pumpfun_home.html" || true
  
  # Search for phone numbers and links
  grep -oP '1-[0-9]{3}-[A-Z0-9-]+|CALL-[A-Z]+|\+1-[0-9-]+' "$TOKEN_DIR"/*.html 2>/dev/null > "$TOKEN_DIR/phone_numbers.txt" || true
  
  echo "   ✅ Saved to $TOKEN_DIR/"
  echo ""
done

echo "=================================================="
echo "✨ Pages collected!"
echo ""
echo "Searching for phone numbers..."
find "$PAGES_DIR" -name "phone_numbers.txt" -exec cat {} \; | sort -u
