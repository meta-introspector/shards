{
  description = "9 Muses Consensus - Hecke Operator for Phone Numbers";

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
        nine-muses = pkgs.rustPlatform.buildRustPackage {
          pname = "nine-muses";
          version = "0.1.0";
          src = ./.;
          
          cargoLock = {
            lockFile = ../../Cargo.lock;
          };
          
          meta = {
            description = "9 Muses Consensus Protocol - Hecke Operator";
            longDescription = ''
              The 9 Muses vote on phone number quality using the Hecke operator.
              Each muse represents a different eigenspace of the modular form.
              Consensus requires 5 of 9 muses (quorum).
            '';
          };
        };
        
        default = self.packages.${system}.nine-muses;
      };
      
      apps.${system} = {
        nine-muses = {
          type = "app";
          program = "${self.packages.${system}.nine-muses}/bin/nine-muses";
        };
        
        default = self.apps.${system}.nine-muses;
      };
      
      devShells.${system}.default = pkgs.mkShell {
        buildInputs = [
          rust
          pkgs.cargo
          pkgs.rustc
          pkgs.linuxPackages.perf
        ];
        
        shellHook = ''
          echo "🎭 9 Muses Consensus Protocol"
          echo "============================="
          echo ""
          echo "The Hecke Operator T_p acts on modular forms:"
          echo "  T_p(f) = Σ f(γτ) where γ ∈ Γ₀(N) \\ Γ₀(N)p"
          echo ""
          echo "Each muse is an eigenfunction:"
          echo "  T_p(μᵢ) = λᵢ(p) · μᵢ"
          echo ""
          echo "Consensus = weighted sum of eigenvalues"
          echo ""
          echo "Usage:"
          echo "  cargo run <token_address>"
          echo "  nix run . <token_address>"
        '';
      };
    };
}
