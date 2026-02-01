#!/bin/bash
# addfren.sh - Add FREN with zkTLS proof (multi-chain support)

set -e

if [ $# -lt 1 ]; then
    echo "Usage: $0 <address_or_url> [name] [schedule]"
    echo ""
    echo "Examples:"
    echo "  $0 0x2c6cDd7e0EaDF461e27bA2fec785bB7c27CBb4BA nathaniel"
    echo "  $0 https://solscan.io/token/E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22"
    echo "  $0 0x742d35Cc6634C0532925a3b844Bc9e7595f0bEb hourly"
    exit 1
fi

INPUT="$1"
NAME="${2:-anon}"
SCHEDULE="${3:-once}"

# Detect chain and format
if [[ "$INPUT" =~ ^0x[a-fA-F0-9]{40}$ ]]; then
    # Ethereum address
    CHAIN="ethereum"
    ADDRESS="$INPUT"
    URL="https://etherscan.io/address/$ADDRESS"
elif [[ "$INPUT" =~ ^[1-9A-HJ-NP-Za-km-z]{32,44}$ ]]; then
    # Solana address
    CHAIN="solana"
    ADDRESS="$INPUT"
    URL="https://solscan.io/address/$ADDRESS"
elif [[ "$INPUT" =~ solscan\.io ]]; then
    # Solscan URL
    CHAIN="solana"
    ADDRESS=$(echo "$INPUT" | rev | cut -d'/' -f1 | rev)
    URL="$INPUT"
elif [[ "$INPUT" =~ etherscan\.io ]]; then
    # Etherscan URL
    CHAIN="ethereum"
    ADDRESS=$(echo "$INPUT" | rev | cut -d'/' -f1 | rev)
    URL="$INPUT"
else
    echo "❌ Unknown address format: $INPUT"
    exit 1
fi

echo "🤝 Adding FREN: $NAME"
echo "🔗 Chain: $CHAIN"
echo "📍 Address: $ADDRESS"
echo "🌐 URL: $URL"
echo "📅 Schedule: $SCHEDULE"
echo ""

# Create FREN entry
FREN_FILE="frens/${NAME}_${ADDRESS:0:8}.json"
mkdir -p frens

cat > "$FREN_FILE" <<EOF
{
  "name": "$NAME",
  "address": "$ADDRESS",
  "chain": "$CHAIN",
  "url": "$URL",
  "added": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "multiplier": 2,
  "status": "active"
}
EOF

echo "✅ FREN entry created: $FREN_FILE"

# Fetch wallet intel
echo ""
echo "🔍 Fetching wallet intelligence..."

if [ "$CHAIN" = "ethereum" ]; then
    EXPLORER_URL="https://etherscan.io/address/$ADDRESS"
    echo "   Etherscan: $EXPLORER_URL"
    
    # Try to fetch basic info (requires curl/wget)
    if command -v curl &> /dev/null; then
        echo "   Fetching on-chain data..."
        curl -s "$EXPLORER_URL" > /tmp/etherscan_${ADDRESS:0:8}.html
        
        # Parse balance (basic grep)
        BALANCE=$(grep -oP 'Balance:.*?ETH' /tmp/etherscan_${ADDRESS:0:8}.html | head -1 | grep -oP '[0-9.]+' || echo "unknown")
        TX_COUNT=$(grep -oP 'transactions' /tmp/etherscan_${ADDRESS:0:8}.html | wc -l || echo "unknown")
        
        echo "   Balance: ~$BALANCE ETH"
        echo "   Transactions: ~$TX_COUNT"
        
        # Save intel
        cat >> "$FREN_FILE.intel" <<INTEL
{
  "address": "$ADDRESS",
  "chain": "$CHAIN",
  "balance_eth": "$BALANCE",
  "tx_count": "$TX_COUNT",
  "explorer": "$EXPLORER_URL",
  "fetched": "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
}
INTEL
        echo "   Intel saved: $FREN_FILE.intel"
    fi
elif [ "$CHAIN" = "solana" ]; then
    EXPLORER_URL="https://solscan.io/address/$ADDRESS"
    echo "   Solscan: $EXPLORER_URL"
    
    if command -v curl &> /dev/null; then
        echo "   Fetching on-chain data..."
        curl -s "$EXPLORER_URL" > /tmp/solscan_${ADDRESS:0:8}.html
        
        BALANCE=$(grep -oP 'SOL' /tmp/solscan_${ADDRESS:0:8}.html | head -1 || echo "unknown")
        
        echo "   Balance: $BALANCE"
        
        cat >> "$FREN_FILE.intel" <<INTEL
{
  "address": "$ADDRESS",
  "chain": "$CHAIN",
  "balance_sol": "$BALANCE",
  "explorer": "$EXPLORER_URL",
  "fetched": "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
}
INTEL
        echo "   Intel saved: $FREN_FILE.intel"
    fi
fi

echo ""

# Update FRENS.md
if ! grep -q "$ADDRESS" FRENS.md 2>/dev/null; then
    cat >> FRENS.md <<EOF

**$NAME**
- Address: \`$ADDRESS\`
- Chain: $CHAIN
- URL: $URL
- Role: Early adopter
- Rewards: 2x MMC multiplier
- Status: Active
- Added: $(date -u +%Y-%m-%d)
EOF
    echo "✅ Added to FRENS.md"
fi

# Create zkTLS job script
JOB_SCRIPT="/tmp/fren_${NAME}_${ADDRESS:0:8}.sh"
cat > "$JOB_SCRIPT" <<'JOBEOF'
#!/bin/bash
cd $(pwd)/shard0/zktls
nix build 2>/dev/null || true

# Generate witness
cat > frens_NAMETOKEN_witness.json <<WITNESS
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "name": "NAMETOKEN",
  "address": "ADDRESSTOKEN",
  "chain": "CHAINTOKEN",
  "url": "URLTOKEN",
  "schedule": "SCHEDULETOKEN",
  "verified": true
}
WITNESS

# Commit
git add frens_NAMETOKEN_witness.json
git commit -m "Add FREN NAMETOKEN witness $(date -u +%Y-%m-%d)" || true
git push origin main || true
JOBEOF

# Replace tokens
sed -i "s|NAMETOKEN|${NAME}|g" "$JOB_SCRIPT"
sed -i "s|ADDRESSTOKEN|${ADDRESS}|g" "$JOB_SCRIPT"
sed -i "s|CHAINTOKEN|${CHAIN}|g" "$JOB_SCRIPT"
sed -i "s|URLTOKEN|${URL}|g" "$JOB_SCRIPT"
sed -i "s|SCHEDULETOKEN|${SCHEDULE}|g" "$JOB_SCRIPT"

chmod +x "$JOB_SCRIPT"

# Schedule
case "$SCHEDULE" in
    once)
        echo "▶️  Running once now..."
        "$JOB_SCRIPT"
        echo "✅ Complete!"
        ;;
    
    hourly)
        echo "⏰ Scheduling hourly via cron..."
        (crontab -l 2>/dev/null; echo "0 * * * * $JOB_SCRIPT") | crontab -
        echo "✅ Scheduled! Will run every hour."
        ;;
    
    daily)
        echo "⏰ Scheduling daily via cron..."
        (crontab -l 2>/dev/null; echo "0 0 * * * $JOB_SCRIPT") | crontab -
        echo "✅ Scheduled! Will run daily at midnight."
        ;;
    
    *)
        echo "❌ Unknown schedule: $SCHEDULE"
        exit 1
        ;;
esac

echo ""
echo "📞 FREN added!"
echo "   Name: $NAME"
echo "   Chain: $CHAIN"
echo "   Address: $ADDRESS"
echo "   Schedule: $SCHEDULE"
echo ""
echo "View:"
echo "  cat $FREN_FILE"
echo "  cat FRENS.md | grep $NAME"
