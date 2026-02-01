{
  description = "Vessel: Nebuchadnezzar - TradeWars BBS Deployment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay.url = "github:oxalica/rust-overlay";
  };

  outputs = { self, nixpkgs, rust-overlay, ... }: {
    devShells.x86_64-linux.default = 
      let
        pkgs = import nixpkgs {
          system = "x86_64-linux";
          overlays = [ rust-overlay.overlays.default ];
        };
      in pkgs.mkShell {
        buildInputs = with pkgs; [
          (rust-bin.stable.latest.default.override {
            extensions = [ "rust-src" ];
            targets = [ "wasm32-unknown-unknown" ];
          })
          solana-cli
          nodejs_20
          dioxus-cli
        ];
        
        shellHook = ''
          echo "🚢 Vessel: Nebuchadnezzar Ready"
          echo "Solana: $(solana --version)"
          solana config set --url https://api.devnet.solana.com
        '';
      };
  };
}
