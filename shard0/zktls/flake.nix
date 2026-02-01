{
  description = "zkTLS FRENS phone generator with witness";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay.url = "github:oxalica/rust-overlay";
  };

  outputs = { self, nixpkgs, rust-overlay }:
    let
      system = "x86_64-linux";
      overlays = [ rust-overlay.overlays.default ];
      pkgs = import nixpkgs { inherit system overlays; };
      rust = pkgs.rust-bin.stable.latest.default;
    in {
      packages.${system} = {
        zktls-frens = pkgs.rustPlatform.buildRustPackage {
          pname = "zktls-frens";
          version = "0.1.0";
          src = ./.;
          
          cargoLock = {
            lockFile = ./Cargo.lock;
            outputHashes = {
              "tlsn-core-0.1.0" = "sha256-AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA=";
            };
          };
          
          nativeBuildInputs = [ pkgs.pkg-config ];
          buildInputs = [ pkgs.openssl ];
        };
        
        default = self.packages.${system}.zktls-frens;
      };
      
      apps.${system} = {
        frens-phone = {
          type = "app";
          program = "${self.packages.${system}.zktls-frens}/bin/frens_phone";
        };
        
        default = self.apps.${system}.frens-phone;
      };
      
      devShells.${system}.default = pkgs.mkShell {
        buildInputs = [
          rust
          pkgs.cargo
          pkgs.rustc
          pkgs.pkg-config
          pkgs.openssl
          pkgs.linuxPackages.perf
        ];
        
        shellHook = ''
          echo "🔐 zkTLS FRENS Phone Generator"
          echo "=============================="
          echo ""
          echo "Usage:"
          echo "  cargo run --bin frens_phone <solscan_url>"
          echo ""
          echo "With perf:"
          echo "  perf record -o frens.perf -- cargo run --bin frens_phone <url>"
          echo ""
          echo "Pipelight:"
          echo "  pipelight run zktls-frens"
        '';
      };
    };
}
