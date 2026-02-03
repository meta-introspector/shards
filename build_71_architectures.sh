#!/bin/bash
# Cross-compile Monster tools to 71 architectures
# AGPL-3.0+ | Commercial: shards@solfunmeme.com

set -e

TARGETS=(
    # x86 family (8 targets)
    "i686-unknown-linux-gnu"
    "x86_64-unknown-linux-gnu"
    "x86_64-unknown-linux-musl"
    "i686-unknown-linux-musl"
    "x86_64-pc-windows-gnu"
    "i686-pc-windows-gnu"
    "x86_64-apple-darwin"
    "i686-apple-darwin"
    
    # ARM family (15 targets)
    "arm-unknown-linux-gnueabi"
    "arm-unknown-linux-gnueabihf"
    "armv7-unknown-linux-gnueabi"
    "armv7-unknown-linux-gnueabihf"
    "aarch64-unknown-linux-gnu"
    "aarch64-unknown-linux-musl"
    "aarch64-apple-darwin"
    "aarch64-apple-ios"
    "armv7-linux-androideabi"
    "aarch64-linux-android"
    "arm-linux-androideabi"
    "thumbv7neon-linux-androideabi"
    "thumbv7neon-unknown-linux-gnueabihf"
    "armv7-unknown-linux-musleabihf"
    "aarch64-unknown-linux-ohos"
    
    # RISC-V (5 targets)
    "riscv32i-unknown-none-elf"
    "riscv32imac-unknown-none-elf"
    "riscv32imc-unknown-none-elf"
    "riscv64gc-unknown-linux-gnu"
    "riscv64imac-unknown-none-elf"
    
    # MIPS (8 targets)
    "mips-unknown-linux-gnu"
    "mipsel-unknown-linux-gnu"
    "mips64-unknown-linux-gnuabi64"
    "mips64el-unknown-linux-gnuabi64"
    "mips-unknown-linux-musl"
    "mipsel-unknown-linux-musl"
    "mips64-unknown-linux-muslabi64"
    "mips64el-unknown-linux-muslabi64"
    
    # PowerPC (6 targets)
    "powerpc-unknown-linux-gnu"
    "powerpc64-unknown-linux-gnu"
    "powerpc64le-unknown-linux-gnu"
    "powerpc-unknown-linux-musl"
    "powerpc64-unknown-linux-musl"
    "powerpc64le-unknown-linux-musl"
    
    # SPARC (3 targets)
    "sparc64-unknown-linux-gnu"
    "sparc-unknown-linux-gnu"
    "sparc64-unknown-netbsd"
    
    # WASM (4 targets)
    "wasm32-unknown-unknown"
    "wasm32-unknown-emscripten"
    "wasm32-wasi"
    "wasm64-unknown-unknown"
    
    # Other architectures (22 targets to reach 71)
    "s390x-unknown-linux-gnu"
    "hexagon-unknown-linux-musl"
    "nvptx64-nvidia-cuda"
    "amdgcn-amd-amdhsa"
    "bpf-unknown-none"
    "msp430-none-elf"
    "avr-unknown-gnu-atmega328"
    "thumbv6m-none-eabi"
    "thumbv7em-none-eabi"
    "thumbv7em-none-eabihf"
    "thumbv7m-none-eabi"
    "thumbv8m.base-none-eabi"
    "thumbv8m.main-none-eabi"
    "thumbv8m.main-none-eabihf"
    "aarch64-unknown-none"
    "aarch64-unknown-none-softfloat"
    "riscv32gc-unknown-linux-gnu"
    "riscv32imc-esp-espidf"
    "xtensa-esp32-none-elf"
    "xtensa-esp32s2-none-elf"
    "xtensa-esp32s3-none-elf"
    "xtensa-esp8266-none-elf"
)

echo "🦀 CROSS-COMPILING TO 71 ARCHITECTURES 🦀"
echo "Target count: ${#TARGETS[@]}"
echo ""

cd rust_tools
mkdir -p ../binaries_71

SUCCESS=0
FAILED=0

for target in "${TARGETS[@]}"; do
    echo "Building for $target..."
    
    # Add target
    rustup target add "$target" 2>/dev/null || true
    
    # Try to build
    if cargo build --release --target "$target" 2>/dev/null; then
        # Copy binary
        BINARY=$(find target/$target/release -maxdepth 1 -type f -executable 2>/dev/null | head -1)
        if [ -n "$BINARY" ]; then
            cp "$BINARY" "../binaries_71/monster-tools-$target" 2>/dev/null || true
            echo "✓ $target"
            ((SUCCESS++))
        else
            echo "✗ $target (no binary)"
            ((FAILED++))
        fi
    else
        echo "✗ $target (build failed)"
        ((FAILED++))
    fi
done

echo ""
echo "================================"
echo "Build complete!"
echo "Success: $SUCCESS"
echo "Failed: $FAILED"
echo "Total: ${#TARGETS[@]}"
echo ""
echo "Binaries in: binaries_71/"
ls -lh ../binaries_71/ 2>/dev/null | head -20
