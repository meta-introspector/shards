{
  description = "Vessel: Nebuchadnezzar - TradeWars BBS + Science Lab";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay.url = "github:oxalica/rust-overlay";
  };

  outputs = { self, nixpkgs, rust-overlay, ... }: {
    devShells.x86_64-linux = {
      # Default: TradeWars + Science Lab
      default = 
        let
          pkgs = import nixpkgs {
            system = "x86_64-linux";
            overlays = [ rust-overlay.overlays.default ];
          };
          
          # Python with science packages
          pythonEnv = pkgs.python311.withPackages (ps: with ps; [
            numpy scipy matplotlib pandas
            sympy networkx
            parquet arrow-cpp pyarrow
          ]);
          
        in pkgs.mkShell {
          buildInputs = with pkgs; [
            # Rust + Solana
            (rust-bin.stable.latest.default.override {
              extensions = [ "rust-src" ];
              targets = [ "wasm32-unknown-unknown" ];
            })
            solana-cli
            nodejs_20
            dioxus-cli
            
            # Science Lab - Math
            gap pari maxima
            
            # Science Lab - Proof
            lean4 z3 cvc5
            
            # Science Lab - Logic
            swiProlog
            
            # Science Lab - Constraint
            minizinc
            
            # Science Lab - Python
            pythonEnv
            
            # Parquet tools
            parquet-tools
            
            # Build tools
            cargo-edit cargo-watch
            pkg-config openssl
            
            # Utils
            bc jq graphviz
          ];
          
          shellHook = ''
            echo "🚢 Vessel: Nebuchadnezzar - Science Lab Loaded 🔬"
            echo "=================================================="
            echo ""
            echo "TradeWars:"
            echo "  Solana: $(solana --version)"
            solana config set --url https://api.devnet.solana.com
            echo ""
            echo "Science Lab:"
            echo "  GAP: $(gap --version 2>&1 | head -1)"
            echo "  Lean4: $(lean --version)"
            echo "  MiniZinc: $(minizinc --version | head -1)"
            echo "  Z3: $(z3 --version)"
            echo "  Python: $(python3 --version)"
            echo ""
            echo "Parquet Tools:"
            echo "  22 Rust analyzers available"
            echo "  LMFDB self-analyzer ready"
            echo ""
            echo "∴ Nebuchadnezzar ready for Monster analysis ✓"
          '';
        };
      
      # Science-only shell
      science = 
        let
          pkgs = import nixpkgs {
            system = "x86_64-linux";
            overlays = [ rust-overlay.overlays.default ];
          };
          
          pythonEnv = pkgs.python311.withPackages (ps: with ps; [
            numpy scipy matplotlib pandas
            sympy networkx
            parquet arrow-cpp pyarrow
          ]);
          
        in pkgs.mkShell {
          buildInputs = with pkgs; [
            rust-bin.stable.latest.default
            gap pari maxima
            lean4 z3 cvc5
            swiProlog minizinc
            pythonEnv
            parquet-tools
            bc jq graphviz
          ];
          
          shellHook = ''
            echo "🔬 Nebuchadnezzar Science Lab Only 🔬"
            echo "GAP + Lean4 + MiniZinc + Z3 + Parquet"
          '';
        };
    };
  };
}
