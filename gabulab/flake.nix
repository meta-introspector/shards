{
  description = "Gabulab: The Yeast of Thought and Mind - Extract Monster Harmonics from Promptbooks";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay.url = "github:oxalica/rust-overlay";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, rust-overlay, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs { inherit system overlays; };
        
        rustToolchain = pkgs.rust-bin.stable.latest.default.override {
          extensions = [ "rust-src" "rust-analyzer" ];
          targets = [ "wasm32-unknown-unknown" ];
        };
        
      in {
        packages = {
          # Rust core
          gabulab-rust = pkgs.rustPlatform.buildRustPackage {
            pname = "gabulab";
            version = "0.1.0";
            src = ./.;
            cargoLock.lockFile = ./Cargo.lock;
            
            nativeBuildInputs = [ rustToolchain ];
            
            meta = {
              description = "Extract Monster Harmonics from Promptbooks";
              license = pkgs.lib.licenses.cc0;
            };
          };
          
          # Lean4 proofs
          gabulab-lean = pkgs.stdenv.mkDerivation {
            pname = "gabulab-lean";
            version = "0.1.0";
            src = ./lean;
            
            buildInputs = [ pkgs.lean4 ];
            
            buildPhase = ''
              lake build
            '';
            
            installPhase = ''
              mkdir -p $out/lib
              cp -r .lake/build/lib/* $out/lib/
            '';
          };
          
          # Prolog queries
          gabulab-prolog = pkgs.stdenv.mkDerivation {
            pname = "gabulab-prolog";
            version = "0.1.0";
            src = ./prolog;
            
            buildInputs = [ pkgs.swiProlog ];
            
            installPhase = ''
              mkdir -p $out/share/prolog
              cp *.pl $out/share/prolog/
            '';
          };
          
          # MiniZinc solver
          gabulab-minizinc = pkgs.stdenv.mkDerivation {
            pname = "gabulab-minizinc";
            version = "0.1.0";
            src = ./minizinc;
            
            buildInputs = [ pkgs.minizinc ];
            
            installPhase = ''
              mkdir -p $out/share/minizinc
              cp *.mzn $out/share/minizinc/
            '';
          };
          
          # WASM bundle
          gabulab-wasm = pkgs.rustPlatform.buildRustPackage {
            pname = "gabulab-wasm";
            version = "0.1.0";
            src = ./.;
            cargoLock.lockFile = ./Cargo.lock;
            
            nativeBuildInputs = [ 
              rustToolchain 
              pkgs.wasm-pack
              pkgs.wasm-bindgen-cli
            ];
            
            buildPhase = ''
              wasm-pack build --target web --out-dir pkg
            '';
            
            installPhase = ''
              mkdir -p $out/share/wasm
              cp -r pkg/* $out/share/wasm/
            '';
          };
          
          # Complete system
          gabulab-all = pkgs.symlinkJoin {
            name = "gabulab-all";
            paths = [
              self.packages.${system}.gabulab-rust
              self.packages.${system}.gabulab-lean
              self.packages.${system}.gabulab-prolog
              self.packages.${system}.gabulab-minizinc
              self.packages.${system}.gabulab-wasm
            ];
          };
          
          default = self.packages.${system}.gabulab-all;
        };
        
        devShells.default = pkgs.mkShell {
          buildInputs = [
            rustToolchain
            pkgs.lean4
            pkgs.swiProlog
            pkgs.minizinc
            pkgs.wasm-pack
            pkgs.wasm-bindgen-cli
            pkgs.nodejs
            pkgs.cargo-watch
          ];
          
          shellHook = ''
            echo "🔮⚡📖 Gabulab: The Yeast of Thought and Mind"
            echo "=============================================="
            echo ""
            echo "Available commands:"
            echo "  cargo build          - Build Rust core"
            echo "  cargo test           - Run tests"
            echo "  wasm-pack build      - Build WASM"
            echo "  lake build           - Build Lean4 proofs"
            echo "  swipl -s prolog/gabulab.pl - Run Prolog"
            echo "  minizinc minizinc/harmonics.mzn - Solve constraints"
            echo ""
          '';
        };
      }
    );
}
