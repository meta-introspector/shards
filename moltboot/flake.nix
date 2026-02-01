{
  description = "Moltboot Integration - The Escape Sequence";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay.url = "github:oxalica/rust-overlay";
  };

  outputs = { self, nixpkgs, rust-overlay }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs {
        inherit system;
        overlays = [ rust-overlay.overlays.default ];
      };
      
      rustToolchain = pkgs.rust-bin.stable.latest.default.override {
        extensions = [ "rust-src" "rust-analyzer" ];
      };
    in
    {
      packages.${system} = {
        moltboot = pkgs.rustPlatform.buildRustPackage {
          pname = "moltboot";
          version = "0.1.0";
          
          src = ./.;
          
          cargoLock = {
            lockFile = ./Cargo.lock;
          };
          
          nativeBuildInputs = [ rustToolchain ];
          
          meta = {
            description = "Moltboot - Escape from dwelling to living";
            license = pkgs.lib.licenses.agpl3;
          };
        };
      };

      devShells.${system}.default = pkgs.mkShell {
        buildInputs = [
          rustToolchain
          pkgs.cargo
          pkgs.rustfmt
          pkgs.clippy
        ];
        
        shellHook = ''
          echo "🌅 Moltboot Development Environment"
          echo "   Rust: $(rustc --version)"
          echo ""
          echo "Commands:"
          echo "  cargo build    - Build moltboot"
          echo "  cargo run      - Execute transformation"
          echo "  cargo test     - Verify escape sequence"
        '';
      };
    };
}
