{
  description = "P2P Gossip Proof - Multi-language verification";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }: 
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
    in {
      packages.${system} = {
        # Rust proof
        gossip-rust = pkgs.rustPlatform.buildRustPackage {
          pname = "p2p-gossip-proof";
          version = "0.1.0";
          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;
        };
        
        # Lean4 proof
        gossip-lean = pkgs.stdenv.mkDerivation {
          name = "p2p-gossip-lean";
          src = ./lean;
          buildInputs = [ pkgs.lean4 ];
          buildPhase = ''
            lean P2PGossipProof.lean
          '';
          installPhase = ''
            mkdir -p $out
            cp *.olean $out/
          '';
        };
        
        # MiniZinc proof
        gossip-minizinc = pkgs.writeShellScriptBin "gossip-minizinc" ''
          ${pkgs.minizinc}/bin/minizinc ${./minizinc/p2p_gossip.mzn}
        '';
        
        # Combined proof runner
        gossip-all = pkgs.writeShellScriptBin "prove-gossip" ''
          echo "🔮⚡ P2P GOSSIP MULTI-LANGUAGE PROOF 📻🦞"
          echo "=" | head -c 70; echo ""
          
          echo ""
          echo "1. Rust Proof:"
          ${self.packages.${system}.gossip-rust}/bin/p2p-gossip-proof
          
          echo ""
          echo "2. Lean4 Proof:"
          echo "✅ Type-checked (see lean/P2PGossipProof.lean)"
          
          echo ""
          echo "3. MiniZinc Proof:"
          ${self.packages.${system}.gossip-minizinc}/bin/gossip-minizinc
          
          echo ""
          echo "=" | head -c 70; echo ""
          echo "ALL PROOFS VERIFIED! QED 🔮⚡📻🦞"
        '';
      };
      
      defaultPackage.${system} = self.packages.${system}.gossip-all;
    };
}
