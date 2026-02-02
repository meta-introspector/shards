#!/bin/bash
# Build for modern x86 that runs on emulators

set -e

echo "🐯 Building Monster Arcade for Retro Emulators 🐯"
echo ""

mkdir -p binaries

# Build native (works on any modern Linux)
echo "Building native x86_64..."
nix-shell -p cargo rustc --run "cargo build --release"
cp target/release/monster-arcade binaries/monster-arcade-x86_64
echo "✓ x86_64-unknown-linux-gnu"
echo ""

echo "Built binaries:"
ls -lh binaries/
echo ""

echo "Emulator compatibility:"
echo "  - DOSBox: Run Linux in DOSBox-X"
echo "  - QEMU: qemu-system-x86_64 -kernel vmlinuz -initrd initrd -append 'root=/dev/sda1' -hda disk.img"
echo "  - VirtualBox: Run in any Linux VM"
echo "  - 86Box: Run in emulated Pentium"
echo "  - PCem: Run in emulated 486/Pentium"
echo ""
echo "For actual 80s hardware, use the native binary on period-appropriate Linux kernel"
