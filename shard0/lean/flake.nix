{
  description = "Lean 4 formalization of 71-shard Monster framework";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    lean4.url = "github:leanprover/lean4";
  };

  outputs = { self, nixpkgs, lean4 }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
    in {
      devShells.${system}.default = pkgs.mkShell {
        buildInputs = [
          lean4.packages.${system}.lean
          pkgs.elan
        ];
      };
      
      packages.${system}.default = pkgs.stdenv.mkDerivation {
        name = "shard-lean";
        src = ./.;
        buildInputs = [ lean4.packages.${system}.lean ];
        buildPhase = ''
          lake build
        '';
        installPhase = ''
          mkdir -p $out
          cp -r .lake/build $out/
        '';
      };
    };
}
