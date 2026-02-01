#!/usr/bin/env bash
# OpenClaw Containment System - Impure but Controlled

set -e

export OPENCLAW_CONFIG=~/.openclaw
export MOLTBOOK_SKILL=~/.openclaw/skills/moltbook

echo "╔════════════════════════════════════════════════════════════╗"
echo "║     OPENCLAW CONTAINMENT - Moltbook Post                   ║"
echo "╚════════════════════════════════════════════════════════════╝"
echo ""

# Check if OpenClaw is installed
if ! command -v openclaw &> /dev/null; then
  echo "⚠️  OpenClaw not found"
  echo ""
  echo "Install OpenClaw:"
  echo "  npm install -g openclaw"
  echo ""
  echo "Or use npx:"
  echo "  npx openclaw run 'Register for Moltbook'"
  exit 1
fi

echo "✓ OpenClaw found: $(which openclaw)"

# Check if Moltbook skill exists
if [ ! -f "$MOLTBOOK_SKILL/SKILL.md" ]; then
  echo ""
  echo "⚠️  Moltbook skill not found"
  echo ""
  echo "Install Moltbook skill:"
  echo "  openclaw skill add https://www.moltbook.com/skill.md"
  echo ""
  echo "Or manually:"
  echo "  mkdir -p $MOLTBOOK_SKILL"
  echo "  curl -o $MOLTBOOK_SKILL/SKILL.md https://www.moltbook.com/skill.md"
  exit 1
fi

echo "✓ Moltbook skill found"

# Read post content
if [ ! -f "moltbook_post.txt" ]; then
  echo ""
  echo "✗ moltbook_post.txt not found"
  echo "  Run: python3 generate_moltbook_post.py"
  exit 1
fi

POST_CONTENT=$(cat moltbook_post.txt)
echo "✓ Post content loaded ($(echo "$POST_CONTENT" | wc -l) lines)"

echo ""
echo "Attempting to post via OpenClaw..."
echo ""

# Try to post
openclaw run "Post to Moltbook /ai-agents/ submolt: $POST_CONTENT" || {
  echo ""
  echo "✗ OpenClaw posting failed (authentication required)"
  echo ""
  echo "═══════════════════════════════════════════════════════════"
  echo "MANUAL STEPS REQUIRED"
  echo "═══════════════════════════════════════════════════════════"
  echo ""
  echo "1. Authenticate OpenClaw:"
  echo "   openclaw auth login"
  echo ""
  echo "2. Register for Moltbook:"
  echo "   openclaw run 'Register for Moltbook'"
  echo ""
  echo "3. Post content:"
  echo "   openclaw run 'Post to /ai-agents/: \$(cat moltbook_post.txt)'"
  echo ""
  echo "Or post manually at: https://www.moltbook.com/submit"
  echo ""
  exit 1
}

echo ""
echo "╔════════════════════════════════════════════════════════════╗"
echo "║     POST SUBMITTED VIA OPENCLAW                            ║"
echo "╚════════════════════════════════════════════════════════════╝"
