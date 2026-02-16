#!/usr/bin/env bash
# Generate archive for Internet Archive upload

set -e

ARCHIVE_NAME="nixwars-tournament-$(date +%Y%m%d-%H%M%S)"
ARCHIVE_DIR="/tmp/$ARCHIVE_NAME"

echo "📦 Generating Nix-Wars Archive"
echo "==============================="
echo ""

# Create archive structure
mkdir -p "$ARCHIVE_DIR"/{site,nix,uucp,parquet}

echo "🎮 Building tournament..."
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"
nix build

# Copy tournament results
cp result "$ARCHIVE_DIR/nix/tournament-results.json"

echo "🌐 Generating static site..."
mkdir -p "$ARCHIVE_DIR/site"
cp -r ../docs/* "$ARCHIVE_DIR/site/"

# Generate tournament HTML
cat > "$ARCHIVE_DIR/site/tournament.html" << 'EOF'
<!DOCTYPE html>
<html>
<head>
  <title>Nix-Wars Tournament - 42 Rounds</title>
  <style>
    body { margin: 0; background: #000; color: #0f0; font-family: monospace; padding: 20px; }
    h1 { color: #0ff; text-align: center; }
    .leaderboard { max-width: 800px; margin: 20px auto; }
    .player { background: #111; padding: 15px; margin: 10px 0; border-left: 3px solid #0f0; }
    .rank { color: #ff0; font-size: 24px; }
    .emoji { font-size: 32px; }
  </style>
</head>
<body>
  <h1>🏆 NIX-WARS TOURNAMENT</h1>
  <div style="text-align: center; margin: 20px;">
    <div>Rounds: <span style="color: #0ff;">42</span></div>
    <div>Players: <span style="color: #0ff;">18</span></div>
  </div>
  <div class="leaderboard">
    <h2>🏆 LEADERBOARD</h2>
EOF

# Add leaderboard
jq -r '.leaderboard[] | "<div class=\"player\"><span class=\"rank\">#\(.rank)</span> <span class=\"emoji\">\(.emoji)</span> <strong>\(.name)</strong><br>Sector: \(.sector) | Credits: \(.credits)</div>"' result >> "$ARCHIVE_DIR/site/tournament.html"

cat >> "$ARCHIVE_DIR/site/tournament.html" << 'EOF'
  </div>
</body>
</html>
EOF

echo "📦 Creating NAR archive..."
nix-store --export $(nix-store -qR result) > "$ARCHIVE_DIR/nix/tournament.nar"

echo "📊 Creating Parquet archive..."
# Convert tournament data to Parquet
python3 << PYEOF
import json
import pyarrow as pa
import pyarrow.parquet as pq

with open('result') as f:
    data = json.load(f)

# Convert leaderboard to Parquet
leaderboard = data['leaderboard']
table = pa.Table.from_pylist(leaderboard)
pq.write_table(table, '$ARCHIVE_DIR/parquet/leaderboard.parquet')

print("✅ Parquet created")
PYEOF

echo "📮 Creating UUCP spool..."
mkdir -p "$ARCHIVE_DIR/uucp/tradewars/tournament"

# Create UUCP message
cat > "$ARCHIVE_DIR/uucp/tradewars/tournament/tournament.msg" << EOF
From: nixwars@localhost
To: archive@archive.org
Subject: Nix-Wars Tournament Results
Date: $(date -R)

Tournament: 42 rounds, 18 players
Winner: $(jq -r '.winner' result)
Commitment: $(jq -r '.commitment[0:16]' result)...

Full results attached.
EOF

cp result "$ARCHIVE_DIR/uucp/tradewars/tournament/results.json"

echo "🗜️  Creating tarball..."
cd /tmp
tar czf "$ARCHIVE_NAME.tar.gz" "$ARCHIVE_NAME"

echo ""
echo "✅ Archive created: /tmp/$ARCHIVE_NAME.tar.gz"
echo "   Size: $(du -h /tmp/$ARCHIVE_NAME.tar.gz | cut -f1)"
echo ""
echo "📤 Upload to Internet Archive:"
echo "   ia upload nixwars-tournament /tmp/$ARCHIVE_NAME.tar.gz \\"
echo "     --metadata='title:Nix-Wars Tournament' \\"
echo "     --metadata='description:42-round tournament with 18 players' \\"
echo "     --metadata='subject:gaming;nix;blockchain;fractran' \\"
echo "     --metadata='date:$(date +%Y-%m-%d)'"
echo ""
echo "📦 Archive contents:"
ls -lh "$ARCHIVE_DIR"/*/ | head -20
