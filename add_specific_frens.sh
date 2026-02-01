#!/usr/bin/env bash
# add_specific_frens.sh - Add specific FREN tokens with metadata
# Usage: ./add_specific_frens.sh

set -euo pipefail

WITNESS_DIR="witnesses/frens"
mkdir -p "$WITNESS_DIR"

echo "🎭 Adding 6 FRENs..."
echo "=================================================="

# FREN 1: E6QQ (original FRENS token)
TOKEN1="E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22"
SHARD1=$((0x$(echo -n "$TOKEN1" | sha256sum | cut -c1-2) % 71))
echo "[1/6] $TOKEN1"
echo "      Shard: $SHARD1 | FRENS (original)"

cat > "$WITNESS_DIR/${TOKEN1}_witness.json" <<EOF
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "operation": "add_fren",
  "token": "$TOKEN1",
  "shard": $SHARD1,
  "metadata": {
    "name": "FRENS",
    "original": true,
    "has_zktls_proof": true,
    "has_muses_consensus": true
  },
  "status": "active"
}
EOF

# FREN 2: BwUT (from solfunmeme archive)
TOKEN2="BwUTq7fS6sfUmHDwAiCQZ3asSiPEapW5zDrsbwtapump"
SHARD2=$((0x$(echo -n "$TOKEN2" | sha256sum | cut -c1-2) % 71))
echo "[2/6] $TOKEN2"
echo "      Shard: $SHARD2 | BwUT (solfunmeme archive)"

cat > "$WITNESS_DIR/${TOKEN2}_witness.json" <<EOF
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "operation": "add_fren",
  "token": "$TOKEN2",
  "shard": $SHARD2,
  "metadata": {
    "name": "BwUT",
    "source": "solfunmeme",
    "archive_date": "2025-04-25",
    "has_rpc_cache": true,
    "rpc_cache_path": "/mnt/data1/meta-introspector/submodules/solfunmeme-introspector/rpc_cache2"
  },
  "status": "active"
}
EOF

# FREN 3: GNBe (bonded)
TOKEN3="GNBe3at5NDpu45z1foWwrVfdxYhFA5dYWqNm2JMVSCAM"
SHARD3=$((0x$(echo -n "$TOKEN3" | sha256sum | cut -c1-2) % 71))
echo "[3/6] $TOKEN3"
echo "      Shard: $SHARD3 | GNBe (bonded)"

cat > "$WITNESS_DIR/${TOKEN3}_witness.json" <<EOF
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "operation": "add_fren",
  "token": "$TOKEN3",
  "shard": $SHARD3,
  "metadata": {
    "name": "GNBe",
    "status": "bonded",
    "notes": "Bonded token"
  },
  "status": "active"
}
EOF

# FREN 4: DD87 (2 other buys)
TOKEN4="DD87KkJH3hJeTC8U3msdrbzwkApmjDrxXA3sTbC7FAKE"
SHARD4=$((0x$(echo -n "$TOKEN4" | sha256sum | cut -c1-2) % 71))
echo "[4/6] $TOKEN4"
echo "      Shard: $SHARD4 | DD87 (2 other buys)"

cat > "$WITNESS_DIR/${TOKEN4}_witness.json" <<EOF
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "operation": "add_fren",
  "token": "$TOKEN4",
  "shard": $SHARD4,
  "metadata": {
    "name": "DD87",
    "activity": "2 other buys",
    "notes": "Has some trading activity"
  },
  "status": "active"
}
EOF

# FREN 5: 9DgK (just me - yikes)
TOKEN5="9DgKaWyhitMG1AtAdAAozy9ZspRUa42omzrZHnHw5FUN"
SHARD5=$((0x$(echo -n "$TOKEN5" | sha256sum | cut -c1-2) % 71))
echo "[5/6] $TOKEN5"
echo "      Shard: $SHARD5 | 9DgK (solo holder - yikes!)"

cat > "$WITNESS_DIR/${TOKEN5}_witness.json" <<EOF
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "operation": "add_fren",
  "token": "$TOKEN5",
  "shard": $SHARD5,
  "metadata": {
    "name": "9DgK",
    "activity": "solo holder",
    "notes": "Just me - that's yikes",
    "lonely": true
  },
  "status": "active"
}
EOF

# FREN 6: Fuj6 (pump token)
TOKEN6="Fuj6EDWQHBnQ3eEvYDujNQ4rPLSkhm3pBySbQ79Bpump"
SHARD6=$((0x$(echo -n "$TOKEN6" | sha256sum | cut -c1-2) % 71))
echo "[6/6] $TOKEN6"
echo "      Shard: $SHARD6 | Fuj6 (pump)"

cat > "$WITNESS_DIR/${TOKEN6}_witness.json" <<EOF
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "operation": "add_fren",
  "token": "$TOKEN6",
  "shard": $SHARD6,
  "metadata": {
    "name": "Fuj6",
    "type": "pump"
  },
  "status": "active"
}
EOF

# FREN 7: 9bzJ (pump token)
TOKEN7="9bzJn2jHQPCGsYKapFvytJQcbaz5FN2TtNB43jb1pump"
SHARD7=$((0x$(echo -n "$TOKEN7" | sha256sum | cut -c1-2) % 71))
echo "[7/7] $TOKEN7"
echo "      Shard: $SHARD7 | 9bzJ (pump)"

cat > "$WITNESS_DIR/${TOKEN7}_witness.json" <<EOF
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "operation": "add_fren",
  "token": "$TOKEN7",
  "shard": $SHARD7,
  "metadata": {
    "name": "9bzJ",
    "type": "pump"
  },
  "status": "active"
}
EOF

echo ""
echo "=================================================="
echo "✨ 7 FRENs added!"
echo ""
echo "Shard distribution:"
echo "  Shard $SHARD1: E6QQ (FRENS original)"
echo "  Shard $SHARD2: BwUT (solfunmeme)"
echo "  Shard $SHARD3: GNBe (bonded)"
echo "  Shard $SHARD4: DD87 (2 buys)"
echo "  Shard $SHARD5: 9DgK (solo - yikes!)"
echo "  Shard $SHARD6: Fuj6 (pump)"
echo "  Shard $SHARD7: 9bzJ (pump)"
echo ""
echo "Total witnesses: $(ls -1 "$WITNESS_DIR"/*.json 2>/dev/null | wc -l)"
echo ""
echo "Next: Run 9 Muses consensus"
echo "  cd shard0/9muses && nix build"
