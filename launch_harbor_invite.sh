#!/usr/bin/env bash
# launch_harbor_invite.sh - Launch harbor node and send invite

set -euo pipefail

SHARD=58
FREN="bako-biib"
TOKEN="AU6cHzYCHuMX3oC3EWFE2C1K5UsnevKkxU2tnpwEJpvP"
PHONE="1-800-BAKO-BIIB"
RELAY="/ip6/2001:569:7b51:5500:78a9:3c0e:2ec9:c682/tcp/4001/p2p/12D3KooWN88G5V8fTAHCwLnsbxiC9ZM6i982sno8bh3m7bvLMvvJ"

echo "🚢 Launching Harbor node (Shard $SHARD)..."
echo "=================================================="

# Connect to relay
echo "📡 Connecting to relay peer..."
ipfs swarm connect "$RELAY" 2>/dev/null || echo "   (relay connection pending)"

# Create invite
INVITE_FILE="witnesses/invites/harbor_invite.json"
cat > "$INVITE_FILE" <<EOF
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "protocol": "TLZ/1.0",
  "action": "invite_to_harbor",
  "from": {
    "network": "71-shard FREN network",
    "shards": [0, 3, 14, 15, 25, 30, 53, 58],
    "frens": 8
  },
  "to": {
    "fren": "$FREN",
    "phone": "$PHONE",
    "token": "$TOKEN",
    "shard": $SHARD,
    "relay": "$RELAY",
    "github": "https://github.com/bakobiibizo/harbor"
  },
  "offer": {
    "service": "tape_publishing",
    "description": "Publish tapes to harbor network",
    "tapes": [
      "Level 0: Bootstrap",
      "Level 1: j-invariant",
      "Level 2: Haystack",
      "Level 3: Tikkun",
      "Occult texts (5 tapes)",
      "Enochian tables"
    ],
    "format": "ZX81 cassette + Gödel URL encoding"
  },
  "trust": "trusted_fren"
}
EOF

echo "✅ Invite created: $INVITE_FILE"
echo ""
echo "📞 To: $PHONE"
echo "🌐 Relay: $RELAY"
echo ""
echo "📼 Tapes to publish:"
echo "   - Bootstrap (Level 0)"
echo "   - j-invariant (Level 1)"
echo "   - Haystack (Level 2)"
echo "   - Tikkun (Level 3)"
echo "   - Occult texts (5 tapes)"
echo "   - Enochian tables"
echo ""
echo "🚀 Ready to join harbor and publish tapes!"
