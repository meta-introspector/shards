#!/bin/bash
# Cross-compile TradeWars scoreboard to all architectures

set -e

echo "🔮⚡ Cross-Compiling TradeWars Scoreboard 📻🦞"
echo "=" | head -c 70; echo ""

cd /home/mdupont/introspector/doorgame

# Targets
TARGETS=(
    "x86_64-unknown-linux-gnu"
    "x86_64-unknown-linux-musl"
    "aarch64-unknown-linux-gnu"
    "armv7-unknown-linux-gnueabihf"
    "i686-unknown-linux-gnu"
    "wasm32-unknown-unknown"
    "wasm32-wasi"
)

echo "Installing targets..."
for target in "${TARGETS[@]}"; do
    rustup target add "$target" 2>/dev/null || echo "  ⚠️  $target (skipped)"
done

echo ""
echo "Building for all architectures..."
mkdir -p builds

for target in "${TARGETS[@]}"; do
    echo ""
    echo "Building: $target"
    
    if [[ "$target" == wasm* ]]; then
        # WASM builds
        cargo build --target "$target" --release 2>/dev/null && \
            cp "target/$target/release/scoreboard.wasm" "builds/scoreboard-$target.wasm" 2>/dev/null || \
            echo "  ⚠️  Build failed (may need wasm-pack)"
    else
        # Native builds
        cargo build --target "$target" --release 2>/dev/null && \
            cp "target/$target/release/scoreboard" "builds/scoreboard-$target" 2>/dev/null || \
            echo "  ⚠️  Build failed (may need cross-compiler)"
    fi
done

echo ""
echo "=" | head -c 70; echo ""
echo "BUILDS COMPLETE!"
echo "=" | head -c 70; echo ""
ls -lh builds/ 2>/dev/null || echo "No builds directory"
echo ""
echo "QED 🔮⚡📻🦞"
