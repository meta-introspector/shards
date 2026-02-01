{
  description = "CICADA-71 with scheduled Hecke-Maass sharding and free-tier AI";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        
        # Free-tier AI CLIs
        gemini-cli = pkgs.writeShellScriptBin "gemini-analyze-shards" ''
          export GEMINI_API_KEY=$(cat ~/.config/gemini/api_key 2>/dev/null || echo "")
          
          if [ -z "$GEMINI_API_KEY" ]; then
            echo "Warning: GEMINI_API_KEY not set"
            exit 0
          fi
          
          ${pkgs.curl}/bin/curl -s https://generativelanguage.googleapis.com/v1beta/models/gemini-pro:generateContent \
            -H "Content-Type: application/json" \
            -H "x-goog-api-key: $GEMINI_API_KEY" \
            -d @- << EOF | ${pkgs.jq}/bin/jq -r '.candidates[0].content.parts[0].text' > gemini_analysis.json
          {
            "contents": [{
              "parts": [{
                "text": "Analyze this Hecke-Maass shard manifest and identify: 1) Imbalanced shards, 2) Files that should be grouped together, 3) Optimization suggestions. Manifest: $(cat HECKE_MAASS_MANIFEST.json)"
              }]
            }]
          }
          EOF
          
          echo "Gemini analysis complete"
        '';
        
        claude-cli = pkgs.writeShellScriptBin "claude-analyze-shards" ''
          export ANTHROPIC_API_KEY=$(cat ~/.config/anthropic/api_key 2>/dev/null || echo "")
          
          if [ -z "$ANTHROPIC_API_KEY" ]; then
            echo "Warning: ANTHROPIC_API_KEY not set"
            exit 0
          fi
          
          ${pkgs.curl}/bin/curl -s https://api.anthropic.com/v1/messages \
            -H "Content-Type: application/json" \
            -H "x-api-key: $ANTHROPIC_API_KEY" \
            -H "anthropic-version: 2023-06-01" \
            -d @- << EOF | ${pkgs.jq}/bin/jq -r '.content[0].text' > claude_analysis.json
          {
            "model": "claude-3-haiku-20240307",
            "max_tokens": 1024,
            "messages": [{
              "role": "user",
              "content": "Analyze this Hecke-Maass shard manifest for mathematical correctness and distribution quality: $(cat HECKE_MAASS_MANIFEST.json | head -c 4000)"
            }]
          }
          EOF
          
          echo "Claude analysis complete"
        '';
        
        openai-cli = pkgs.writeShellScriptBin "gpt-analyze-shards" ''
          export OPENAI_API_KEY=$(cat ~/.config/openai/api_key 2>/dev/null || echo "")
          
          if [ -z "$OPENAI_API_KEY" ]; then
            echo "Warning: OPENAI_API_KEY not set"
            exit 0
          fi
          
          ${pkgs.curl}/bin/curl -s https://api.openai.com/v1/chat/completions \
            -H "Content-Type: application/json" \
            -H "Authorization: Bearer $OPENAI_API_KEY" \
            -d @- << EOF | ${pkgs.jq}/bin/jq -r '.choices[0].message.content' > gpt_analysis.json
          {
            "model": "gpt-3.5-turbo",
            "messages": [{
              "role": "user",
              "content": "Analyze Hecke eigenvalue distribution: $(cat HECKE_MAASS_MANIFEST.json | ${pkgs.jq}/bin/jq -c '.shards[] | {shard_id, file_count, total_weighted_norm}')"
            }],
            "max_tokens": 500
          }
          EOF
          
          echo "GPT analysis complete"
        '';
        
        ollama-cli = pkgs.writeShellScriptBin "ollama-analyze-shards" ''
          # Check if Ollama is running
          if ! ${pkgs.curl}/bin/curl -s http://localhost:11434/api/tags >/dev/null 2>&1; then
            echo "Warning: Ollama not running"
            exit 0
          fi
          
          ${pkgs.curl}/bin/curl -s http://localhost:11434/api/generate \
            -d @- << EOF | ${pkgs.jq}/bin/jq -r '.response' > ollama_analysis.json
          {
            "model": "llama3.2",
            "prompt": "Analyze this shard distribution for balance and correctness: $(cat HECKE_MAASS_MANIFEST.json | ${pkgs.jq}/bin/jq -c '.shards[0:10]')",
            "stream": false
          }
          EOF
          
          echo "Ollama analysis complete"
        '';
        
        ai-consensus = pkgs.writeShellScriptBin "ai-consensus" ''
          ${pkgs.python3}/bin/python3 ${./ai_consensus.py}
        '';
        
      in {
        devShells = {
          default = pkgs.mkShell {
            buildInputs = with pkgs; [
              python3
              curl
              jq
              git
              pipelight
            ];
            
            shellHook = ''
              echo "CICADA-71 Development Environment"
              echo "Run: pipelight run swab_deck"
            '';
          };
          
          gemini-cli = pkgs.mkShell {
            buildInputs = [ gemini-cli pkgs.curl pkgs.jq ];
          };
          
          claude-cli = pkgs.mkShell {
            buildInputs = [ claude-cli pkgs.curl pkgs.jq ];
          };
          
          openai-cli = pkgs.mkShell {
            buildInputs = [ openai-cli pkgs.curl pkgs.jq ];
          };
          
          ollama = pkgs.mkShell {
            buildInputs = [ ollama-cli pkgs.curl pkgs.jq ];
          };
        };
        
        packages = {
          inherit gemini-cli claude-cli openai-cli ollama-cli ai-consensus;
          
          swab-deck = pkgs.writeShellScriptBin "swab-deck" ''
            ${./swab_the_deck.sh}
          '';
        };
        
        apps = {
          swab = {
            type = "app";
            program = "${self.packages.${system}.swab-deck}/bin/swab-deck";
          };
        };
      }
    );
}
