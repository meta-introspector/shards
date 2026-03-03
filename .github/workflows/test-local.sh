#!/usr/bin/env bash
# Test GitHub Action locally with act

set -e

echo "🧪 Testing GitHub Action Locally"
echo "================================="
echo ""

# Check if act is installed
if ! command -v act &> /dev/null; then
    echo "📦 Installing act (nektos/act)..."
    nix-env -iA nixpkgs.act || {
        echo "Installing via curl..."
        curl https://raw.githubusercontent.com/nektos/act/master/install.sh | sudo bash
    }
fi

# Create test event
cat > /tmp/test-event.json << 'EOF'
{
  "ref": "refs/heads/nydiokar/main",
  "repository": {
    "name": "shards",
    "owner": {
      "name": "meta-introspector"
    }
  }
}
EOF

# Create secrets file (without real keys for testing)
cat > /tmp/test-secrets << 'EOF'
IA_ACCESS_KEY=test_access_key
IA_SECRET_KEY=test_secret_key
EOF

echo "🏃 Running workflow locally..."
echo ""

cd /home/mdupont/projects/cicadia71/shards

# Run only the build-tournament job (skip deploy)
act push \
  --job build-tournament \
  --eventpath /tmp/test-event.json \
  --secret-file /tmp/test-secrets \
  --platform ubuntu-latest=catthehacker/ubuntu:act-latest \
  --verbose

echo ""
echo "✅ Local test complete!"
echo ""
echo "To test full workflow with real secrets:"
echo "  1. Create ~/.actrc with:"
echo "     -s IA_ACCESS_KEY=<your_key>"
echo "     -s IA_SECRET_KEY=<your_secret>"
echo "  2. Run: act push --job deploy"
