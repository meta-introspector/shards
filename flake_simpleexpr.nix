{
  description = "SimpleExpr Monster Tower: MiniZinc + Rust + Lean4";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
    in {
      packages.${system}.default = pkgs.rustPlatform.buildRustPackage {
        pname = "simpleexpr-monster";
        version = "0.1.0";
        src = ./.;
        cargoLock.lockFile = ./Cargo.lock;
      };

      devShells.${system}.default = pkgs.mkShell {
        packages = with pkgs; [
          minizinc
          rustc
          cargo
          lean4
        ];
      };
    };
}
