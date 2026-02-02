{
  description = "CICADA-71 Moltbook Integration";

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
        extensions = [ "rust-src" ];
      };
    in
    {
      packages.${system} = {
        cicada-moltbook = pkgs.rustPlatform.buildRustPackage {
          pname = "cicada-moltbook";
          version = "0.1.0";
          
          src = ./.;
          
          cargoLock = {
            lockFile = ./Cargo.lock;
          };
          
          nativeBuildInputs = [ rustToolchain ];
          
          meta = {
            description = "CICADA-71 joins Moltbook - The Agent Internet";
            homepage = "https://github.com/meta-introspector/shards";
          };
        };
        
        default = self.packages.${system}.cicada-moltbook;
      };
      
      devShells.${system}.default = pkgs.mkShell {
        buildInputs = [
          rustToolchain
          pkgs.cargo
          pkgs.rustc
        ];
      };
    };
}
