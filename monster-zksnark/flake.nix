{
  description = "Monster Harmonic zkSNARK - Circom proof system";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in {
        packages = {
          # Circom compiler
          circom = pkgs.circom;
          
          # snarkjs CLI
          snarkjs = pkgs.nodePackages.snarkjs;
          
          # Monster Harmonic proof generator
          monster-proof = pkgs.writeShellScriptBin "monster-proof" ''
            set -e
            
            SHARD_ID=''${1:-0}
            WITNESS_PATH="$HOME/.openclaw/shard-$SHARD_ID/zkwitness-$SHARD_ID.json"
            CIRCUIT_DIR="$HOME/introspector"
            OUTPUT_DIR="$HOME/.openclaw/shard-$SHARD_ID"
            
            echo "🔷 Monster Harmonic zkSNARK Proof Generator"
            echo "═══════════════════════════════════════════"
            echo "Shard: $SHARD_ID"
            echo ""
            
            # Generate Circom witness
            echo "📊 Generating Circom witness..."
            ${pkgs.python3}/bin/python3 "$CIRCUIT_DIR/generate_monster_witness.py" "$WITNESS_PATH"
            
            # Compile circuit
            if [ ! -f "$OUTPUT_DIR/monster_harmonic.r1cs" ]; then
              echo "🔧 Compiling Circom circuit..."
              cd "$CIRCUIT_DIR"
              ${pkgs.circom}/bin/circom monster_harmonic.circom \
                --r1cs \
                --wasm \
                --sym \
                -o "$OUTPUT_DIR"
            fi
            
            # Generate witness
            echo "🔢 Computing witness..."
            cd "$OUTPUT_DIR/monster_harmonic_js"
            ${pkgs.nodejs}/bin/node generate_witness.js \
              monster_harmonic.wasm \
              "$OUTPUT_DIR/monster_witness.json" \
              "$OUTPUT_DIR/witness.wtns"
            
            # Powers of Tau
            if [ ! -f "$OUTPUT_DIR/pot_final.ptau" ]; then
              echo "⚡ Powers of Tau ceremony..."
              ${pkgs.nodePackages.snarkjs}/bin/snarkjs powersoftau new bn128 14 "$OUTPUT_DIR/pot_0000.ptau" -v
              ${pkgs.nodePackages.snarkjs}/bin/snarkjs powersoftau contribute "$OUTPUT_DIR/pot_0000.ptau" \
                "$OUTPUT_DIR/pot_0001.ptau" --name="Monster" -v -e="$(date +%s)"
              ${pkgs.nodePackages.snarkjs}/bin/snarkjs powersoftau prepare phase2 "$OUTPUT_DIR/pot_0001.ptau" \
                "$OUTPUT_DIR/pot_final.ptau" -v
            fi
            
            # Groth16 setup
            if [ ! -f "$OUTPUT_DIR/monster_harmonic_final.zkey" ]; then
              echo "🔑 Groth16 setup..."
              ${pkgs.nodePackages.snarkjs}/bin/snarkjs groth16 setup \
                "$OUTPUT_DIR/monster_harmonic.r1cs" \
                "$OUTPUT_DIR/pot_final.ptau" \
                "$OUTPUT_DIR/monster_harmonic_0000.zkey"
              
              ${pkgs.nodePackages.snarkjs}/bin/snarkjs zkey contribute \
                "$OUTPUT_DIR/monster_harmonic_0000.zkey" \
                "$OUTPUT_DIR/monster_harmonic_final.zkey" \
                --name="Monster" -v -e="$(date +%s)"
              
              ${pkgs.nodePackages.snarkjs}/bin/snarkjs zkey export verificationkey \
                "$OUTPUT_DIR/monster_harmonic_final.zkey" \
                "$OUTPUT_DIR/verification_key.json"
            fi
            
            # Generate proof
            echo "🔐 Generating zkSNARK proof..."
            ${pkgs.nodePackages.snarkjs}/bin/snarkjs groth16 prove \
              "$OUTPUT_DIR/monster_harmonic_final.zkey" \
              "$OUTPUT_DIR/witness.wtns" \
              "$OUTPUT_DIR/proof.json" \
              "$OUTPUT_DIR/public.json"
            
            # Verify
            echo "✅ Verifying proof..."
            ${pkgs.nodePackages.snarkjs}/bin/snarkjs groth16 verify \
              "$OUTPUT_DIR/verification_key.json" \
              "$OUTPUT_DIR/public.json" \
              "$OUTPUT_DIR/proof.json"
            
            echo ""
            echo "✅ Monster Harmonic proof generated!"
            echo "   Proof: $OUTPUT_DIR/proof.json"
            echo "   Public: $OUTPUT_DIR/public.json"
          '';
          
          default = self.packages.${system}.monster-proof;
        };
        
        apps = {
          monster-proof = {
            type = "app";
            program = "${self.packages.${system}.monster-proof}/bin/monster-proof";
          };
          
          default = self.apps.${system}.monster-proof;
        };
        
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            circom
            nodePackages.snarkjs
            nodejs
            python3
            jq
          ];
          
          shellHook = ''
            echo "🔷 Monster Harmonic zkSNARK Environment"
            echo "════════════════════════════════════════"
            echo ""
            echo "Available commands:"
            echo "  nix run .#monster-proof -- <shard_id>"
            echo "  circom --version"
            echo "  snarkjs --version"
            echo ""
          '';
        };
      }
    );
}
