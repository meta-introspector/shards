{
  description = "TradeWars Scoreboard - Multi-arch builds";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay.url = "github:oxalica/rust-overlay";
  };

  outputs = { self, nixpkgs, rust-overlay }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "i686-linux" ];
      
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f system);
    in {
      packages = forAllSystems (system:
        let
          pkgs = import nixpkgs {
            inherit system;
            overlays = [ rust-overlay.overlays.default ];
          };
          
          rust = pkgs.rust-bin.stable.latest.default.override {
            targets = [
              "x86_64-unknown-linux-gnu"
              "x86_64-unknown-linux-musl"
              "aarch64-unknown-linux-gnu"
              "armv7-unknown-linux-gnueabihf"
              "i686-unknown-linux-gnu"
              "wasm32-unknown-unknown"
              "wasm32-wasi"
            ];
          };
        in {
          scoreboard = pkgs.rustPlatform.buildRustPackage {
            pname = "tradewars-scoreboard";
            version = "0.1.0";
            src = ./.;
            cargoLock.lockFile = ./Cargo.lock;
            nativeBuildInputs = [ rust ];
          };
          
          scoreboard-wasm = pkgs.rustPlatform.buildRustPackage {
            pname = "tradewars-scoreboard-wasm";
            version = "0.1.0";
            src = ./.;
            cargoLock.lockFile = ./Cargo.lock;
            nativeBuildInputs = [ rust pkgs.wasm-pack ];
            buildPhase = ''
              wasm-pack build --target web
            '';
            installPhase = ''
              mkdir -p $out
              cp pkg/*.wasm $out/
              cp pkg/*.js $out/
            '';
          };
          
          all-archs = pkgs.writeShellScriptBin "build-all" ''
            ${./build_all_archs.sh}
          '';
        });
      
      defaultPackage = forAllSystems (system: 
        self.packages.${system}.scoreboard
      );
    };
}
