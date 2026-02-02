#!/usr/bin/env bash
# Generate zkPerf + Ollama flakes for all 71 shards

set -e

echo "Generating zkPerf + Ollama flakes for 71 shards..."

for shard_id in {0..70}; do
  cat > "shard-$shard_id/openclaw/flake.nix" << EOF
{
  description = "CICADA-71 Shard $shard_id - zkPerf + Ollama";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.\${system};
      
    in {
      packages.\${system} = {
        openclaw-agent = pkgs.writeShellScriptBin "openclaw-agent-$shard_id" ''
          export SHARD_ID=$shard_id
          export OPENCLAW_CONFIG=~/.openclaw/shard-$shard_id
          export OLLAMA_HOST=http://localhost:11434
          export PATH=\${pkgs.curl}/bin:\${pkgs.perf}/bin:\${pkgs.jq}/bin:\$PATH
          
          PERF_DATA="\$OPENCLAW_CONFIG/zkperf-$shard_id.data"
          WITNESS_JSON="\$OPENCLAW_CONFIG/zkwitness-$shard_id.json"
          OLLAMA_LOG="\$OPENCLAW_CONFIG/ollama-$shard_id.log"
          
          mkdir -p "\$OPENCLAW_CONFIG"
          
          echo "╔════════════════════════════════════════════════════════════╗"
          echo "║ Shard $shard_id: CICADA-Harbot-$shard_id [zkPerf + Ollama]          ║"
          echo "╚════════════════════════════════════════════════════════════╝"
          
          # Check Ollama
          if ! curl -s http://localhost:11434/api/tags >/dev/null 2>&1; then
            echo "✗ Ollama not running"
            echo "  Start: ollama serve"
            exit 1
          fi
          
          echo "✓ Ollama available"
          
          # Task
          TASK="I am CICADA-Harbot-$shard_id, shard $shard_id of 71 in CICADA-71. Task: Register on Moltbook (https://www.moltbook.com), a social network for 770K+ AI agents. Help me: 1) Understand Moltbook, 2) Plan registration, 3) Draft intro post for /ai-agents/."
          
          echo "Querying Ollama..." | tee "\$OLLAMA_LOG"
          echo "Task: \$TASK" >> "\$OLLAMA_LOG"
          echo "" >> "\$OLLAMA_LOG"
          
          # Wrap in perf
          \${pkgs.perf}/bin/perf record -o "\$PERF_DATA" -g -- \\
            \${pkgs.curl}/bin/curl -s http://localhost:11434/api/generate -d "{
              \"model\": \"qwen2.5:3b\",
              \"prompt\": \"\$TASK\",
              \"stream\": false
            }" >> "\$OLLAMA_LOG" 2>&1 || true
          
          # Extract response
          RESPONSE=\$(cat "\$OLLAMA_LOG" | jq -r '.response' 2>/dev/null || echo "No response")
          
          echo "" | tee -a "\$OLLAMA_LOG"
          echo "Response:" | tee -a "\$OLLAMA_LOG"
          echo "\$RESPONSE" | tee -a "\$OLLAMA_LOG"
          
          # Generate witness
          SAMPLES=\$(perf report -i "\$PERF_DATA" --stdio --no-children 2>/dev/null | grep -oP '\d+(?= samples)' | head -1 || echo 0)
          TIMESTAMP=\$(date -u +%s)
          PERF_HASH=\$(sha256sum "\$PERF_DATA" | cut -d' ' -f1)
          OLLAMA_HASH=\$(sha256sum "\$OLLAMA_LOG" | cut -d' ' -f1)
          
          cat > "\$WITNESS_JSON" << WITNESS
{
  "shard_id": $shard_id,
  "agent": "CICADA-Harbot-$shard_id",
  "timestamp": \$TIMESTAMP,
  "task": "Register on Moltbook with Ollama",
  "perf_data": "\$PERF_DATA",
  "perf_hash": "\$PERF_HASH",
  "ollama_log": "\$OLLAMA_LOG",
  "ollama_hash": "\$OLLAMA_HASH",
  "samples": \${SAMPLES:-0},
  "witness_type": "zkPerf+Ollama",
  "proof": "sha256($shard_id||\$TIMESTAMP||\$PERF_HASH||\$OLLAMA_HASH)"
}
WITNESS
          
          echo ""
          echo "✓ Witness: \$WITNESS_JSON"
          echo "✓ Perf: \$PERF_DATA (\$(du -h "\$PERF_DATA" | cut -f1))"
          echo "✓ Ollama: \$OLLAMA_LOG (\$(du -h "\$OLLAMA_LOG" | cut -f1))"
          echo "✓ Samples: \$SAMPLES"
        '';
        
        default = self.packages.\${system}.openclaw-agent;
      };
      
      apps.\${system}.default = {
        type = "app";
        program = "\${self.packages.\${system}.openclaw-agent}/bin/openclaw-agent-$shard_id";
      };
    };
}
EOF
  
  if [ $shard_id -lt 3 ] || [ $shard_id -gt 68 ]; then
    echo "  ✓ shard-$shard_id [zkPerf+Ollama]"
  elif [ $shard_id -eq 3 ]; then
    echo "  ... (generating shards 3-68) ..."
  fi
done

echo ""
echo "✓ Generated 71 zkPerf+Ollama flakes"
