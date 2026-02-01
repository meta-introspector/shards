#!/usr/bin/env bash
# Generate flake.nix for all 71 shards

set -e

echo "Generating flake.nix for 71 shards..."

for shard_id in {0..70}; do
  cat > "shard-$shard_id/openclaw/flake.nix" << EOF
{
  description = "CICADA-71 Shard $shard_id - OpenClaw Impure Containment";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.\${system};
      shard_id = $shard_id;
      
    in {
      packages.\${system} = {
        openclaw-agent = pkgs.writeShellScriptBin "openclaw-agent-\${toString shard_id}" ''
          export SHARD_ID=\${toString shard_id}
          export OPENCLAW_CONFIG=~/.openclaw/shard-\${toString shard_id}
          export PATH=\${pkgs.nodejs}/bin:\${pkgs.curl}/bin:\$PATH
          
          echo "Shard \${toString shard_id}: CICADA-Harbot-\${toString shard_id}"
          
          mkdir -p "\$OPENCLAW_CONFIG"
          
          if ! command -v openclaw &> /dev/null; then
            \${pkgs.nodejs}/bin/npm install -g openclaw
          fi
          
          openclaw run "I am CICADA-Harbot-\${toString shard_id}, shard \${toString shard_id} of 71. Register for Moltbook."
        '';
        
        default = self.packages.\${system}.openclaw-agent;
      };
      
      apps.\${system}.default = {
        type = "app";
        program = "\${self.packages.\${system}.openclaw-agent}/bin/openclaw-agent-\${toString shard_id}";
      };
    };
}
EOF
  
  if [ $shard_id -lt 5 ] || [ $shard_id -gt 67 ]; then
    echo "  ✓ shard-$shard_id/openclaw/flake.nix"
  elif [ $shard_id -eq 5 ]; then
    echo "  ... (generating shards 5-67) ..."
  fi
done

echo ""
echo "✓ Generated 71 flake.nix files"
echo ""
echo "Usage:"
echo "  cd shard-0/openclaw && nix run"
echo "  cd shard-27/openclaw && nix run"
echo "  cd shard-70/openclaw && nix run"
