{
  description = "71-Shard Monster Group Framework";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay.url = "github:oxalica/rust-overlay";
    pipelight.url = "github:meta-introspector/pipelight";
  };

  outputs = { self, nixpkgs, flake-utils, rust-overlay, pipelight }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlays = [ rust-overlay.overlays.default ];
        pkgs = import nixpkgs { inherit system overlays; };
        rust = pkgs.rust-bin.stable.latest.default.override {
          extensions = [ "rust-src" "rust-analyzer" ];
        };
      in {
        packages = {
          # Shard 0: Hash ingestion
          shard0-hash = pkgs.rustPlatform.buildRustPackage {
            pname = "shard0-hash";
            version = "0.1.0";
            src = ./shard0/hash;
            cargoLock.lockFile = ./shard0/hash/Cargo.lock;
            nativeBuildInputs = [ pkgs.pkg-config ];
            buildInputs = [ pkgs.openssl ];
          };

          # Shard 0: Cryptanalysis
          shard0-cryptanalysis = pkgs.rustPlatform.buildRustPackage {
            pname = "shard0-cryptanalysis";
            version = "0.1.0";
            src = ./shard0/cryptanalysis;
            cargoLock.lockFile = ./shard0/cryptanalysis/Cargo.lock;
          };

          # Shard 0: P2P networking
          shard0-p2p = pkgs.rustPlatform.buildRustPackage {
            pname = "shard0-p2p";
            version = "0.1.0";
            src = ./shard0/p2p;
            cargoLock.lockFile = ./shard0/p2p/Cargo.lock;
          };

          # Shard 0: FHE
          shard0-fhe = pkgs.rustPlatform.buildRustPackage {
            pname = "shard0-fhe";
            version = "0.1.0";
            src = ./shard0/fhe;
            cargoLock.lockFile = ./shard0/fhe/Cargo.lock;
            buildInputs = [ pkgs.clang pkgs.llvm ];
          };

          # Erlang telecom
          shard0-telecom = pkgs.stdenv.mkDerivation {
            pname = "shard0-telecom";
            version = "0.1.0";
            src = ./shard0/telecom;
            buildInputs = [ pkgs.erlang pkgs.rebar3 ];
            buildPhase = "rebar3 compile";
            installPhase = ''
              mkdir -p $out
              cp -r _build/default/lib/shard_telecom $out/
            '';
          };

          # Lean 4 proofs
          shard0-lean = pkgs.stdenv.mkDerivation {
            pname = "shard0-lean";
            version = "0.1.0";
            src = ./shard0/lean;
            buildInputs = [ pkgs.elan ];
            buildPhase = "lake build";
            installPhase = ''
              mkdir -p $out
              cp -r .lake/build $out/
            '';
          };

          # Documentation site
          docs = pkgs.stdenv.mkDerivation {
            pname = "monster-docs";
            version = "0.1.0";
            src = ./.;
            buildInputs = [ pkgs.mdbook ];
            buildPhase = ''
              mkdir -p book/src
              cp *.md book/src/
              cat > book/book.toml <<EOF
              [book]
              title = "71-Shard Monster Group Framework"
              authors = ["Monster Group Research"]
              language = "en"
              
              [output.html]
              git-repository-url = "https://github.com/meta-introspector/shards"
              EOF
              
              cd book && mdbook build
            '';
            installPhase = ''
              mkdir -p $out
              cp -r book/book/* $out/
            '';
          };

          default = pkgs.symlinkJoin {
            name = "monster-shards";
            paths = [
              self.packages.${system}.shard0-hash
              self.packages.${system}.shard0-cryptanalysis
              self.packages.${system}.shard0-p2p
              self.packages.${system}.shard0-fhe
              self.packages.${system}.shard0-telecom
              self.packages.${system}.shard0-lean
            ];
          };
        };

        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            rust
            cargo
            rustc
            pkg-config
            openssl
            erlang
            rebar3
            elan
            mdbook
            git
            pipelight.packages.${system}.default
          ];

          shellHook = ''
            echo "🎯 Monster Group 71-Shard Framework"
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
            echo "Build:     nix build"
            echo "Develop:   nix develop"
            echo "Pipeline:  pipelight run"
            echo "Docs:      nix build .#docs && firefox result/index.html"
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
          '';
        };

        apps.default = {
          type = "app";
          program = "${self.packages.${system}.default}/bin/shard-analyzer";
        };
      }
    );
}
