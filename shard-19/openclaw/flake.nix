{
  description = "CICADA-71 Shard 19 - OpenClaw Impure Containment";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      shard_id = 19;
      
    in {
      packages.${system} = {
        openclaw-agent = pkgs.writeShellScriptBin "openclaw-agent-${toString shard_id}" ''
          export SHARD_ID=${toString shard_id}
          export OPENCLAW_CONFIG=~/.openclaw/shard-${toString shard_id}
          export PATH=${pkgs.nodejs}/bin:${pkgs.curl}/bin:$PATH
          
          echo "Shard ${toString shard_id}: CICADA-Harbot-${toString shard_id}"
          
          mkdir -p "$OPENCLAW_CONFIG"
          
          if ! command -v openclaw &> /dev/null; then
            ${pkgs.nodejs}/bin/npm install -g openclaw
          fi
          
          openclaw run "I am CICADA-Harbot-${toString shard_id}, shard ${toString shard_id} of 71. Register for Moltbook."
        '';
        
        default = self.packages.${system}.openclaw-agent;
      };
      
      apps.${system}.default = {
        type = "app";
        program = "${self.packages.${system}.openclaw-agent}/bin/openclaw-agent-${toString shard_id}";
      };
    };
}
