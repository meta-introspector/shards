{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  buildInputs = with pkgs; [
    rustc
    cargo
    minizinc
    lean4
    python3
    linuxPackages.perf
  ];
  
  shellHook = ''
    echo "🎮 Mother's Wisdom Build Environment"
    echo "  ✓ Rust: $(rustc --version)"
    echo "  ✓ MiniZinc: $(minizinc --version | head -1)"
    echo "  ✓ Lean4: $(lean --version)"
    echo "  ✓ Python: $(python3 --version)"
    echo "  ✓ Perf: $(perf --version)"
  '';
}
