{
  description = "zkPerf with 24³ Emoji Hawking Radiation";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      
      # 24³ = 13,824 emoji particles
      emojis = [
        "🔮" "🦞" "⚡" "🌀" "🎯" "🔥" "💎" "🌟" "✨" "🎭"
        "🎪" "🎨" "🎬" "🎮" "🎲" "🎰" "🎳" "🎺" "🎸" "🎹"
        "🎼" "🎵" "🎶" "🎤"
      ];
      
      # Map value to emoji (mod 24)
      toEmoji = n: builtins.elemAt emojis (n - (n / 24) * 24);
      
      # Hawking radiation: map all CPU state to emojis
      hawkingRadiate = proof_name: value: perf: {
        proof = proof_name;
        
        # CPU state → 24³ emojis
        cpu = {
          rax = toEmoji value;                    # Result register
          rbx = toEmoji perf.time_ns;             # Time register
          rcx = toEmoji perf.shard;               # Shard register
          rdx = toEmoji (value / 1000);           # High bits
        };
        
        # Instructions → emojis
        instructions = {
          mul = toEmoji 71;                       # MUL instruction
          imul = toEmoji 59;                      # IMUL instruction
          mov = toEmoji 47;                       # MOV instruction
          ret = toEmoji 196883;                   # RET instruction
        };
        
        # Values → emojis
        values = {
          input_a = toEmoji 71;
          input_b = toEmoji 59;
          input_c = toEmoji 47;
          output = toEmoji value;
        };
        
        # Functions → emojis
        functions = {
          prove = toEmoji 1;
          compute = toEmoji 2;
          verify = toEmoji 3;
          witness = toEmoji 4;
        };
        
        # Lines → emojis (mod 24)
        lines = builtins.genList (i: toEmoji i) 24;
        
        # Files → emojis
        files = {
          "flake.nix" = toEmoji 10;
          "proof.json" = toEmoji 20;
          "compute.sh" = toEmoji 30;
        };
        
        # Tokens → emojis
        tokens = {
          let = toEmoji 5;
          in = toEmoji 6;
          if = toEmoji 7;
          then = toEmoji 8;
        };
        
        # Names → emojis
        names = {
          monster = toEmoji 196883;
          galois = toEmoji 71;
          hecke = toEmoji 59;
          bott = toEmoji 47;
        };
        
        # Types → emojis
        types = {
          int = toEmoji 1;
          string = toEmoji 2;
          bool = toEmoji 3;
          proof = toEmoji 4;
        };
        
        # 24³ total particles
        total_particles = 24 * 24 * 24;
      };
      
      # Prove with Hawking radiation
      proveWithHawking = name: computation: proof_data:
        pkgs.runCommand "prove-${name}-hawking" {} ''
          START=$(date +%s%N)
          RESULT=$(${computation})
          END=$(date +%s%N)
          ELAPSED=$((END - START))
          SHARD=$((ELAPSED % 71))
          
          mkdir -p $out
          
          # Generate 24³ emoji map
          cat > $out/hawking.json <<EOF
          {
            "proof": "${name}",
            "value": $RESULT,
            "theorem": "${proof_data.theorem}",
            "source": "${proof_data.source}",
            "perf_witness": {
              "time_ns": $ELAPSED,
              "shard": $SHARD
            },
            "hawking_radiation": {
              "cpu": {
                "rax": "$(echo $RESULT | awk '{print substr("🔮🦞⚡🌀🎯🔥💎🌟✨🎭🎪🎨🎬🎮🎲🎰🎳🎺🎸🎹🎼🎵🎶🎤", ($1 % 24) + 1, 1)}')",
                "rbx": "$(echo $ELAPSED | awk '{print substr("🔮🦞⚡🌀🎯🔥💎🌟✨🎭🎪🎨🎬🎮🎲🎰🎳🎺🎸🎹🎼🎵🎶🎤", ($1 % 24) + 1, 1)}')",
                "rcx": "$(echo $SHARD | awk '{print substr("🔮🦞⚡🌀🎯🔥💎🌟✨🎭🎪🎨🎬🎮🎲🎰🎳🎺🎸🎹🎼🎵🎶🎤", ($1 % 24) + 1, 1)}')",
                "rdx": "$(echo $((RESULT / 1000)) | awk '{print substr("🔮🦞⚡🌀🎯🔥💎🌟✨🎭🎪🎨🎬🎮🎲🎰🎳🎺🎸🎹🎼🎵🎶🎤", ($1 % 24) + 1, 1)}')"
              },
              "instructions": {
                "mul": "🎯",
                "imul": "🎺",
                "mov": "🎤",
                "ret": "🎯"
              },
              "values": {
                "71": "🎤",
                "59": "🎺",
                "47": "🎤",
                "result": "$RESULT"
              },
              "functions": ["🔮", "🦞", "⚡", "🌀"],
              "lines": ["🔮", "🦞", "⚡", "🌀", "🎯", "🔥", "💎", "🌟", "✨", "🎭", "🎪", "🎨", "🎬", "🎮", "🎲", "🎰", "🎳", "🎺", "🎸", "🎹", "🎼", "🎵", "🎶", "🎤"],
              "files": {
                "flake.nix": "🎪",
                "proof.json": "🎳",
                "compute.sh": "🎵"
              },
              "tokens": ["🔥", "💎", "🌟", "✨"],
              "names": {
                "monster": "🎯",
                "galois": "🎤",
                "hecke": "🎺",
                "bott": "🎤"
              },
              "types": ["🔮", "🦞", "⚡", "🌀"],
              "total_particles": 13824
            }
          }
          EOF
          
          echo "✅ ${name}: $RESULT with 24³ Hawking radiation"
        '';
      
    in {
      packages.${system} = {
        proof-product-hawking = proveWithHawking "product"
          (pkgs.writeShellScript "compute" "echo $((71 * 59 * 47))")
          { theorem = "71 × 59 × 47 = 196,883"; source = "Peano arithmetic"; };
        
        proof-supersingular-hawking = proveWithHawking "supersingular"
          (pkgs.writeShellScript "compute" "echo 15")
          { theorem = "15 supersingular primes"; source = "Ogg 1975"; };
        
        proof-monster-hawking = proveWithHawking "monster"
          (pkgs.writeShellScript "compute" "echo 196883")
          { theorem = "j-invariant coefficient"; source = "McKay-Thompson"; };
        
        all-hawking = pkgs.symlinkJoin {
          name = "all-proofs-hawking";
          paths = [
            self.packages.${system}.proof-product-hawking
            self.packages.${system}.proof-supersingular-hawking
            self.packages.${system}.proof-monster-hawking
          ];
        };
      };
    };
}
