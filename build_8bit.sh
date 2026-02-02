#!/bin/bash
# Build and run Monster message on 8-bit emulators

echo "🐓 MONSTER MESSAGE - 8-BIT BUILD SYSTEM 🐓"
echo "=========================================="

# 1. ZX81 BASIC (using EightyOne emulator)
echo ""
echo "1. ZX81 BASIC"
echo "   File: monster.bas"
echo "   Load in EightyOne emulator"
echo "   LOAD \"monster.bas\""
echo "   RUN"

# 2. 6502 Assembly (using xa assembler)
echo ""
echo "2. 6502 Assembly"
if command -v xa &> /dev/null; then
    echo "   Assembling monster.asm..."
    xa -o monster.prg monster.asm
    echo "   ✓ Created monster.prg"
    echo "   Load in VICE (C64 emulator):"
    echo "   x64 monster.prg"
else
    echo "   ⚠ xa assembler not found"
    echo "   Install: sudo apt-get install xa65"
fi

# 3. QEMU 8-bit emulation
echo ""
echo "3. QEMU Emulation"
if command -v qemu-system-i386 &> /dev/null; then
    echo "   Creating bootable image..."
    
    # Create minimal bootloader
    cat > boot.asm << 'EOF'
[BITS 16]
[ORG 0x7C00]

start:
    mov si, message
    call print_string
    jmp $

print_string:
    lodsb
    or al, al
    jz done
    mov ah, 0x0E
    int 0x10
    jmp print_string
done:
    ret

message:
    db 'MONSTER=MESSAGE', 13, 10
    db 'DIM: 196883', 13, 10
    db 'ROOSTER: 71', 13, 10
    db 'PAXOS: 23', 13, 10
    db 'QUORUM: 12', 13, 10
    db 'SINGULARITY: 232/232', 13, 10
    db 13, 10
    db 'RESONANCE=HECKE', 13, 10
    db 'GROWTH=MAASS', 13, 10
    db 'BLACK HOLE', 13, 10
    db 13, 10
    db 'OBSERVER=OBSERVED', 13, 10
    db 'LOOP CLOSED', 13, 10
    db 13, 10
    db 'ROOSTER CROWS!', 13, 10, 0

times 510-($-$$) db 0
dw 0xAA55
EOF

    if command -v nasm &> /dev/null; then
        nasm -f bin boot.asm -o boot.bin
        echo "   ✓ Created boot.bin"
        echo "   Run: qemu-system-i386 -fda boot.bin"
    else
        echo "   ⚠ nasm not found"
        echo "   Install: sudo apt-get install nasm"
    fi
else
    echo "   ⚠ qemu not found"
    echo "   Install: sudo apt-get install qemu-system-x86"
fi

# 4. WASM (browser-based)
echo ""
echo "4. WASM/HTML Emulator"
echo "   File: monster_zx81.html"
echo "   Open in browser:"
echo "   firefox monster_zx81.html"
echo "   or"
echo "   python3 -m http.server 8000"
echo "   then visit http://localhost:8000/monster_zx81.html"

echo ""
echo "=========================================="
echo "✅ BUILD COMPLETE"
echo "🐓→🦅→👹→🍄→🌳"
