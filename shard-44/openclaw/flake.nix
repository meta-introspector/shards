{
  description = "CICADA-71 Shard 44 - OpenClaw + zkPerf Witness";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      shard_id = 44;
      
    in {
      packages.${system} = {
        openclaw-agent = pkgs.writeShellScriptBin "openclaw-agent-${toString shard_id}" ''
          export 44=${toString shard_id}
          export OPENCLAW_CONFIG=~/.openclaw/shard-${toString shard_id}
          export PATH=${pkgs.nodejs}/bin:${pkgs.curl}/bin:${pkgs.linuxPackages.perf}/bin:$PATH
          
          PERF_DATA="$OPENCLAW_CONFIG/zkperf-${toString shard_id}.data"
          WITNESS_JSON="$OPENCLAW_CONFIG/zkwitness-${toString shard_id}.json"
          
          mkdir -p "$OPENCLAW_CONFIG"
          
          echo "╔════════════════════════════════════════════════════════════╗"
          echo "║ Shard ${toString shard_id}: CICADA-Harbot-${toString shard_id} [zkPerf]              ║"
          echo "╚════════════════════════════════════════════════════════════╝"
          
          if ! command -v openclaw &> /dev/null; then
            ${pkgs.nodejs}/bin/npm install -g openclaw
          fi
          
          # Wrap in perf record
          ${pkgs.linuxPackages.perf}/bin/perf record -o "$PERF_DATA" -g -- \
            openclaw run "I am CICADA-Harbot-${toString shard_id}, shard ${toString shard_id} of 71. Register for Moltbook." || true
          
          # Generate zkPerf witness
          SAMPLES=$(perf report -i "$PERF_DATA" --stdio --no-children 2>/dev/null | grep -oP '\d+(?= samples)' | head -1 || echo 0)
          TIMESTAMP=$(date -u +%s)
          HASH=$(sha256sum "$PERF_DATA" | cut -d' ' -f1)
          
          cat > "$WITNESS_JSON" << WITNESS
{
  "shard_id": ${toString shard_id},
  "agent": "CICADA-Harbot-${toString shard_id}",
  "timestamp": $TIMESTAMP,
  "perf_data": "$PERF_DATA",
  "perf_hash": "$HASH",
  "samples": $SAMPLES,
  "witness_type": "zkPerf",
  "proof": "sha256(${toString shard_id} || $TIMESTAMP || $HASH)"
}
WITNESS
          
          echo ""
          echo "✓ zkPerf witness: $WITNESS_JSON"
          echo "✓ Perf data: $PERF_DATA ($(du -h "$PERF_DATA" | cut -f1))"
          echo "✓ Samples: $SAMPLES"
          echo "✓ Hash: $HASH"
        '';
        
        default = self.packages.${system}.openclaw-agent;
      };
      
      apps.${system}.default = {
        type = "app";
        program = "${self.packages.${system}.openclaw-agent}/bin/openclaw-agent-${toString shard_id}";
      };
    };
}
