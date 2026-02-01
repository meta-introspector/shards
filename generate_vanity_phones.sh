#!/usr/bin/env bash
# generate_vanity_phones.sh - Generate vanity phone numbers for FRENs
# Uses token names and properties to create memorable numbers

set -euo pipefail

PHONE_DIR="witnesses/phones"
mkdir -p "$PHONE_DIR"

echo "📞 Generating vanity phone numbers for FRENs..."
echo "=================================================="

# Token name to phone mapping (T9 keypad)
# 2=ABC 3=DEF 4=GHI 5=JKL 6=MNO 7=PQRS 8=TUV 9=WXYZ

# FREN 1: E6QQ - FRENS original
TOKEN1="E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22"
PHONE1="1-800-FRENS-71"  # 1-800-373-6771
cat > "$PHONE_DIR/${TOKEN1}_phone.json" <<EOF
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "token": "$TOKEN1",
  "shard": 53,
  "phone": "$PHONE1",
  "vanity": "1-800-FRENS-71",
  "numeric": "1-800-373-6771",
  "type": "vanity",
  "meaning": "FRENS + 71 shards"
}
EOF
echo "[1/7] E6QQ → $PHONE1"

# FREN 2: BwUT - solfunmeme
TOKEN2="BwUTq7fS6sfUmHDwAiCQZ3asSiPEapW5zDrsbwtapump"
PHONE2="1-800-SOL-MEME"  # 1-800-765-6363
cat > "$PHONE_DIR/${TOKEN2}_phone.json" <<EOF
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "token": "$TOKEN2",
  "shard": 30,
  "phone": "$PHONE2",
  "vanity": "1-800-SOL-MEME",
  "numeric": "1-800-765-6363",
  "type": "vanity",
  "meaning": "Solana meme token"
}
EOF
echo "[2/7] BwUT → $PHONE2"

# FREN 3: GNBe - bonded
TOKEN3="GNBe3at5NDpu45z1foWwrVfdxYhFA5dYWqNm2JMVSCAM"
PHONE3="1-800-BONDED-1"  # 1-800-266-3331
cat > "$PHONE_DIR/${TOKEN3}_phone.json" <<EOF
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "token": "$TOKEN3",
  "shard": 3,
  "phone": "$PHONE3",
  "vanity": "1-800-BONDED-1",
  "numeric": "1-800-266-3331",
  "type": "vanity",
  "meaning": "Bonded token"
}
EOF
echo "[3/7] GNBe → $PHONE3"

# FREN 4: DD87 - 2 buys
TOKEN4="DD87KkJH3hJeTC8U3msdrbzwkApmjDrxXA3sTbC7FAKE"
PHONE4="1-800-TWO-BUYS"  # 1-800-896-2897
cat > "$PHONE_DIR/${TOKEN4}_phone.json" <<EOF
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "token": "$TOKEN4",
  "shard": 14,
  "phone": "$PHONE4",
  "vanity": "1-800-TWO-BUYS",
  "numeric": "1-800-896-2897",
  "type": "vanity",
  "meaning": "2 other buyers"
}
EOF
echo "[4/7] DD87 → $PHONE4"

# FREN 5: 9DgK - solo (yikes)
TOKEN5="9DgKaWyhitMG1AtAdAAozy9ZspRUa42omzrZHnHw5FUN"
PHONE5="1-800-SO-ALONE"  # 1-800-762-5663
cat > "$PHONE_DIR/${TOKEN5}_phone.json" <<EOF
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "token": "$TOKEN5",
  "shard": 15,
  "phone": "$PHONE5",
  "vanity": "1-800-SO-ALONE",
  "numeric": "1-800-762-5663",
  "type": "vanity",
  "meaning": "Solo holder - yikes!"
}
EOF
echo "[5/7] 9DgK → $PHONE5"

# FREN 6: Fuj6 - pump
TOKEN6="Fuj6EDWQHBnQ3eEvYDujNQ4rPLSkhm3pBySbQ79Bpump"
PHONE6="1-800-PUMP-FUN"  # 1-800-786-7386
cat > "$PHONE_DIR/${TOKEN6}_phone.json" <<EOF
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "token": "$TOKEN6",
  "shard": 25,
  "phone": "$PHONE6",
  "vanity": "1-800-PUMP-FUN",
  "numeric": "1-800-786-7386",
  "type": "vanity",
  "meaning": "Pump.fun token"
}
EOF
echo "[6/7] Fuj6 → $PHONE6"

# FREN 7: 9bzJ - pump
TOKEN7="9bzJn2jHQPCGsYKapFvytJQcbaz5FN2TtNB43jb1pump"
PHONE7="1-800-MOON-NOW"  # 1-800-666-6669
cat > "$PHONE_DIR/${TOKEN7}_phone.json" <<EOF
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "token": "$TOKEN7",
  "shard": 0,
  "phone": "$PHONE7",
  "vanity": "1-800-MOON-NOW",
  "numeric": "1-800-666-6669",
  "type": "vanity",
  "meaning": "To the moon!"
}
EOF
echo "[7/7] 9bzJ → $PHONE7"

echo ""
echo "=================================================="
echo "✨ Vanity phone numbers generated!"
echo ""
echo "FREN VANITY DIRECTORY:"
echo "  1-800-FRENS-71  → E6QQ (Shard 53) - FRENS + 71 shards"
echo "  1-800-SOL-MEME  → BwUT (Shard 30) - Solana meme"
echo "  1-800-BONDED-1  → GNBe (Shard 3)  - Bonded token"
echo "  1-800-TWO-BUYS  → DD87 (Shard 14) - 2 buyers"
echo "  1-800-SO-ALONE  → 9DgK (Shard 15) - Solo holder"
echo "  1-800-PUMP-FUN  → Fuj6 (Shard 25) - Pump.fun"
echo "  1-800-MOON-NOW  → 9bzJ (Shard 0)  - To the moon!"
echo ""
echo "Total: 7 vanity numbers"
