# flake.nix - TradeWars BBS Solana Devnet
{
  description = "TradeWars BBS - Solana Devnet Deployment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay.url = "github:oxalica/rust-overlay";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, rust-overlay, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs {
          inherit system overlays;
        };
        
        rustToolchain = pkgs.rust-bin.stable.latest.default.override {
          extensions = [ "rust-src" "rust-analyzer" ];
          targets = [ "wasm32-unknown-unknown" ];
        };

        solana = pkgs.solana-cli;
        anchor = pkgs.stdenv.mkDerivation {
          name = "anchor-cli";
          src = pkgs.fetchFromGitHub {
            owner = "coral-xyz";
            repo = "anchor";
            rev = "v0.29.0";
            sha256 = "sha256-AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA=";
          };
          buildInputs = [ rustToolchain pkgs.pkg-config pkgs.openssl ];
          installPhase = ''
            cargo install --path cli --root $out
          '';
        };

      in {
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            # Rust
            rustToolchain
            cargo-watch
            
            # Solana
            solana-cli
            
            # Anchor (build from source or use binary)
            nodejs_20
            yarn
            
            # WASM
            wasm-pack
            wasm-bindgen-cli
            
            # Dioxus
            dioxus-cli
            
            # Tools
            pkg-config
            openssl
            libudev-zero
            
            # Vercel
            nodePackages.vercel
          ];

          shellHook = ''
            echo "🚀 TradeWars BBS Development Environment"
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
            echo "Solana: $(solana --version)"
            echo "Rust: $(rustc --version)"
            echo "Node: $(node --version)"
            echo ""
            echo "Commands:"
            echo "  nix develop          - Enter dev shell"
            echo "  ./scripts/deploy.sh  - Deploy to devnet"
            echo "  ./scripts/test.sh    - Run tests"
            echo "  ./scripts/build.sh   - Build all"
            echo ""
            
            # Setup Solana
            export SOLANA_NETWORK=devnet
            solana config set --url https://api.devnet.solana.com
            
            # Setup Anchor
            export ANCHOR_WALLET=~/.config/solana/id.json
            
            # Setup Node
            export PATH="$PWD/node_modules/.bin:$PATH"
          '';
        };

        packages = {
          # Anchor program
          tradewars-program = pkgs.stdenv.mkDerivation {
            name = "tradewars-bbs-program";
            src = ./programs/tradewars-bbs;
            
            buildInputs = [ rustToolchain solana ];
            
            buildPhase = ''
              cargo build-bpf --manifest-path Cargo.toml
            '';
            
            installPhase = ''
              mkdir -p $out/bin
              cp target/deploy/*.so $out/bin/
            '';
          };

          # Dioxus frontend
          tradewars-frontend = pkgs.stdenv.mkDerivation {
            name = "tradewars-bbs-frontend";
            src = ./frontend;
            
            buildInputs = [ rustToolchain wasm-pack dioxus-cli ];
            
            buildPhase = ''
              dx build --release
            '';
            
            installPhase = ''
              mkdir -p $out
              cp -r dist/* $out/
            '';
          };
        };

        apps = {
          deploy = {
            type = "app";
            program = "${pkgs.writeShellScript "deploy" ''
              #!/usr/bin/env bash
              set -e
              
              echo "🚀 Deploying to Solana Devnet..."
              
              # Build program
              cd programs/tradewars-bbs
              cargo build-bpf
              
              # Deploy
              solana program deploy target/deploy/tradewars_bbs.so
              
              # Get program ID
              PROGRAM_ID=$(solana-keygen pubkey target/deploy/tradewars_bbs-keypair.json)
              echo "Program ID: $PROGRAM_ID"
              
              # Build frontend
              cd ../../frontend
              dx build --release
              
              # Deploy to Vercel
              vercel deploy --prod
              
              echo "✅ Deployment complete!"
            ''}";
          };

          test = {
            type = "app";
            program = "${pkgs.writeShellScript "test" ''
              #!/usr/bin/env bash
              set -e
              
              echo "🧪 Running tests..."
              
              # Test Anchor program
              cd programs/tradewars-bbs
              cargo test-bpf
              
              # Test frontend
              cd ../../frontend
              cargo test
              
              echo "✅ All tests passed!"
            ''}";
          };
        };
      }
    );
}
