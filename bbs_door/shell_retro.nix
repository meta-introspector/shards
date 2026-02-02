{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  buildInputs = with pkgs; [
    rustc
    cargo
    rustup
    
    # Cross-compilation toolchains
    pkgsCross.i686-embedded.buildPackages.gcc
    pkgsCross.arm-embedded.buildPackages.gcc
    pkgsCross.mips-linux-gnu.buildPackages.gcc
    pkgsCross.powerpc-embedded.buildPackages.gcc
    
    # Emulators for testing
    qemu
    dosbox
    vice      # C64 emulator
    basiliskii # Mac 68k emulator
  ];
  
  shellHook = ''
    echo "🐯 Monster Arcade Retro Build Environment 🐯"
    echo ""
    echo "Available targets:"
    echo "  - i386/i586/i686 (IBM PC)"
    echo "  - m68k (Amiga, Mac)"
    echo "  - powerpc (Mac, Amiga)"
    echo "  - mips/mipsel (SGI, DEC)"
    echo "  - arm (Acorn Archimedes)"
    echo "  - sparc64 (Sun)"
    echo ""
    echo "Run: ./build_retro.sh"
  '';
}
