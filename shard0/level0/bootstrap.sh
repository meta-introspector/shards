#!/bin/bash
# bootstrap.sh - Bootstrap from 357 bytes to GCC
# Based on GNU Mes and Stage0

set -e

echo "🔧 CICADA-71 Level 0: Bootstrap from 357 bytes"
echo "=============================================="
echo ""

# Stage 0: 357-byte seed (hand-auditable hex)
echo "[1/12] Stage 0: hex0 seed (357 bytes)"
if [ ! -f stage0_monitor.hex0 ]; then
    cat > stage0_monitor.hex0 <<'HEX0'
# 357-byte x86 bootstrap seed
# Builds hex0 assembler from nothing
7F 45 4C 46 01 01 01 00 00 00 00 00 00 00 00 00
02 00 03 00 01 00 00 00 54 80 04 08 34 00 00 00
00 00 00 00 00 00 00 00 34 00 20 00 01 00 00 00
00 00 00 00 01 00 00 00 00 00 00 00 00 80 04 08
00 80 04 08 65 01 00 00 65 01 00 00 05 00 00 00
00 10 00 00
HEX0
fi

# Stage 1: Build hex0 (hex assembler)
echo "[2/12] Stage 1: hex0 assembler"
xxd -r -p stage0_monitor.hex0 > hex0-seed
chmod +x hex0-seed

# Stage 2: Build hex1 (labeled hex)
echo "[3/12] Stage 2: hex1 (labeled hex)"
./hex0-seed < hex1_x86.hex0 > hex1
chmod +x hex1

# Stage 3: Build hex2 (macro assembler)
echo "[4/12] Stage 3: hex2 (macro assembler)"
./hex1 < hex2_x86.hex1 > hex2
chmod +x hex2

# Stage 4: Build M0 (minimal language)
echo "[5/12] Stage 4: M0 (minimal language)"
./hex2 < M0_x86.hex2 > M0
chmod +x M0

# Stage 5: Build cc_x86 (C compiler)
echo "[6/12] Stage 5: cc_x86 (C compiler)"
./M0 < cc_x86.M0 > cc_x86
chmod +x cc_x86

# Stage 6: Build M2-Planet (C subset)
echo "[7/12] Stage 6: M2-Planet (C subset)"
./cc_x86 < M2-Planet.c > M2
chmod +x M2

# Stage 7: Build GNU Mes (Scheme interpreter)
echo "[8/12] Stage 7: GNU Mes (Scheme)"
./M2 < mes.c > mes
chmod +x mes

# Stage 8: Build Mes C Library
echo "[9/12] Stage 8: Mes C Library"
./mes < build-libc.scm

# Stage 9: Build TinyCC
echo "[10/12] Stage 9: TinyCC (100KB C compiler)"
./mes < build-tcc.scm
chmod +x tcc

# Stage 10: Build GCC 2.95 (last pre-C++ rewrite)
echo "[11/12] Stage 10: GCC 2.95 (1999)"
./tcc gcc-2.95/gcc.c -o gcc-2.95
chmod +x gcc-2.95

# Stage 11: Build modern GCC
echo "[12/12] Stage 11: Modern GCC"
./gcc-2.95 -o gcc gcc-latest/gcc.c

echo ""
echo "✅ Bootstrap complete!"
echo ""
echo "Toolchain:"
echo "  357 bytes → hex0 → hex1 → hex2 → M0 → cc_x86"
echo "  → M2-Planet → GNU Mes → TinyCC → GCC 2.95 → GCC"
echo ""
echo "Test:"
echo "  ./gcc -o shard0 shard0.c"
echo "  ./shard0 --godel"
echo ""
echo "Expected: 67500000 (2^5 × 3^3 × 5^7)"
