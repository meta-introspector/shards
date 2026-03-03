{
  description = "SOLFUNMEME: Metameme FRACTRAN ecosystem, sharded 71×59×47 with Crowning Ceremony";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    git71.url = "path:../git71";
    umbral-engine.url = "path:../umbral-engine";
  };

  outputs = { self, nixpkgs, git71, umbral-engine }: let
    pkgs = nixpkgs.legacyPackages.x86_64-linux;

    # 71×59×47 = 196,883 shards (Monster group dimension)
    totalShards = 71 * 59 * 47;

    # FRACTRAN shard generator with Hawking radiation
    generateShard = shardId: let
      s71 = shardId / (59 * 47);
      s59 = (shardId / 47) % 59;
      s47 = shardId % 47;
    in ''
      #!/bin/bash
      # FRACTRAN Shard: ${toString shardId}
      # Decomposition: [${toString s71}, ${toString s59}, ${toString s47}]
      # Shard primes: 71 (author), 59 (repo), 47 (file)
      # ADE class: AIII (Chiral symmetry)
      # Leech lattice: 24D coordinates
      # Muses: 9 Greek muses bless this shard
      # Mnemosyne: Memory of all shards

      # Initial state (all supersingular primes)
      state=$((2*3*5*7*11*13*17*19*23*29*31*41*47*59*71))

      # FRACTRAN fractions (Monster moonshine)
      fractions=(
        "2*5/1"       # S∘I: Player1 activates Witness1
        "3*7/1"       # K∘Y: Player2 activates Witness2
        "59*2/1"      # M∘S: Memory update / vote (repo shard)
        "71*3/1"      # N∘K: Shard prime enforcement (author shard)
        "47*23*29/1"  # U∘A∘E: File shard + Paxos + evaluation
        "17*11*13/1"  # W∘B∘C: Muse dance / meme mutation
      )

      # Hawking radiation from zkPerf
      emit_hawking_radiation() {
        local cycles=$1
        local emoji=("🔥" "❄️" "⚡" "💧" "🌊" "🌪️" "☀️" "🌙" "🧠" "💭" "🎯" "🔮" "✨" "🌌" "🎭" "🎨")
        echo "''${emoji[$((cycles % 16))]}"
      }

      # Iterate FRACTRAN
      iterate() {
        local cycles=0
        for fraction in "''${fractions[@]}"; do
          local num=$(echo "$fraction" | cut -d'/' -f1)
          local den=$(echo "$fraction" | cut -d'/' -f2)
          
          if (( state % den == 0 )); then
            state=$((state * num / den))
            cycles=$((cycles + 1000))
            echo "$(emit_hawking_radiation $cycles) State: $state | Cycles: $cycles | Shard: ${toString shardId}"
          fi
        done
        
        # Normalize mod 71 (Monster cap)
        state=$((state % 71))
        echo "✨ Final state (mod 71): $state"
      }

      # Run iteration
      echo "🔮 SOLFUNMEME Shard ${toString shardId} starting..."
      echo "📊 Decomposition: [${toString s71}, ${toString s59}, ${toString s47}]"
      iterate
      echo "✅ Shard ${toString shardId} complete"
    '';

  in
  {
    packages.x86_64-linux = rec {

      # Generate all 196,883 shards as independent packages
      shards = builtins.listToAttrs (builtins.map (id: {
        name = "shard-${toString id}";
        value = pkgs.writeShellScriptBin "shard-${toString id}" (generateShard id);
      }) (builtins.genList (i: i) totalShards));

      # Crowning ceremony runner
      crown-all-shards = pkgs.writeShellScriptBin "crown-all-shards" ''
        echo "👑 CROWNING CEREMONY: All ${toString totalShards} shards"
        echo "=================================================="
        echo ""
        echo "🌌 24^71 Witnesses in Leech lattice"
        echo "🎯 71×59×47 = ${toString totalShards} Monster shards"
        echo "✨ Each shard runs FRACTRAN with Hawking radiation"
        echo ""
        
        # Run first 71 shards (one per author)
        for i in $(seq 0 70); do
          echo ""
          echo "👑 Crowning shard $i..."
          ${self.packages.x86_64-linux.shards."shard-$i"}/bin/shard-$i
        done
        
        echo ""
        echo "✨ First 71 shards crowned!"
        echo "🎯 Remaining $((${toString totalShards} - 71)) shards available"
      '';

      # Interactive door game for specific shard
      door-game = shardId: pkgs.writeShellScriptBin "door-game-${toString shardId}" ''
        echo "╔════════════════════════════════════════════════════════════════╗"
        echo "║     👑 CROWNING DOOR GAME - Shard ${toString shardId}                    ║"
        echo "╚════════════════════════════════════════════════════════════════╝"
        echo ""
        
        # Run FRACTRAN shard
        ${self.packages.x86_64-linux.shards."shard-${toString shardId}"}/bin/shard-${toString shardId}
        
        echo ""
        echo "🎮 Door game complete for shard ${toString shardId}"
        echo "✨ Hawking radiation fountain witnessed"
      '';

      defaultPackage = crown-all-shards;
    };

    apps.x86_64-linux = {
      default = {
        type = "app";
        program = "${self.packages.x86_64-linux.crown-all-shards}/bin/crown-all-shards";
      };
      
      # Run specific shard
      shard = shardId: {
        type = "app";
        program = "${self.packages.x86_64-linux.shards."shard-${toString shardId}"}/bin/shard-${toString shardId}";
      };
    };
  };
}
