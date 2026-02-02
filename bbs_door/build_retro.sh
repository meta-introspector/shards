#!/bin/bash
# Cross-compile Monster Arcade for 80s computer architectures

set -e

TARGETS=(
    # 8-bit era
    "i386-unknown-linux-gnu"           # IBM PC/XT (8088/8086)
    "i586-unknown-linux-gnu"           # IBM PC/AT (80286/386)
    
    # 16-bit era  
    "i686-unknown-linux-gnu"           # 486/Pentium
    
    # Commodore Amiga (68k)
    "m68k-unknown-linux-gnu"
    
    # Apple II / Mac (68k)
    "powerpc-unknown-linux-gnu"
    
    # MIPS (SGI, DEC)
    "mips-unknown-linux-gnu"
    "mipsel-unknown-linux-gnu"
    
    # ARM (Acorn Archimedes)
    "arm-unknown-linux-gnueabi"
    "armv7-unknown-linux-gnueabihf"
    
    # SPARC (Sun workstations)
    "sparc64-unknown-linux-gnu"
)

echo "🐯 Building Monster Arcade for 80s Computer Emulators 🐯"
echo ""

mkdir -p binaries

for target in "${TARGETS[@]}"; do
    echo "Building for $target..."
    
    # Add target if not installed
    rustup target add "$target" 2>/dev/null || true
    
    # Cross-compile
    if cargo build --release --target "$target" 2>/dev/null; then
        cp "target/$target/release/monster-arcade" "binaries/monster-arcade-$target"
        echo "✓ $target"
    else
        echo "✗ $target (skipped - requires cross-compiler)"
    fi
    echo ""
done

echo ""
echo "Built binaries:"
ls -lh binaries/
echo ""
echo "Total architectures: ${#TARGETS[@]}"
