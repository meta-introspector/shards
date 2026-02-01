#!/usr/bin/env bash
# Build and serve WASM BBS

set -e

echo "🔨 Building WASM BBS..."
cd wasm-bbs

# Install wasm-pack if needed
if ! command -v wasm-pack &> /dev/null; then
    echo "📦 Installing wasm-pack..."
    curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh
fi

# Build WASM
wasm-pack build --target web

echo ""
echo "✅ Build complete!"
echo ""
echo "🌐 Starting server..."
echo "   Open: http://localhost:8080"
echo ""

# Serve with Python
python3 -m http.server 8080
