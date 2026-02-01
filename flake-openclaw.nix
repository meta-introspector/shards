{
  description = "CICADA-71 with OpenClaw impure containment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        
        # OpenClaw impure containment
        openclaw-post = pkgs.writeShellScriptBin "openclaw-post" ''
          export PATH=${pkgs.nodejs}/bin:${pkgs.curl}/bin:$PATH
          export OPENCLAW_CONFIG=~/.openclaw
          
          echo "╔════════════════════════════════════════════════════════════╗"
          echo "║     OPENCLAW IMPURE CONTAINMENT                            ║"
          echo "╚════════════════════════════════════════════════════════════╝"
          
          # Check OpenClaw
          if ! command -v openclaw &> /dev/null; then
            echo "Installing OpenClaw..."
            npm install -g openclaw || {
              echo "✗ Install failed. Run manually: npm install -g openclaw"
              exit 1
            }
          fi
          
          echo "✓ OpenClaw available"
          
          # Post to Moltbook
          openclaw run "Register for Moltbook and post: $(cat ${./moltbook_post.txt})" || {
            echo ""
            echo "✗ Posting failed (requires authentication)"
            echo ""
            echo "Manual steps:"
            echo "  1. openclaw auth login"
            echo "  2. openclaw skill add moltbook"
            echo "  3. openclaw run 'Register for Moltbook'"
            echo "  4. openclaw run 'Post: \$(cat moltbook_post.txt)'"
          }
        '';
        
      in {
        packages = {
          openclaw-post = openclaw-post;
          default = openclaw-post;
        };
        
        apps = {
          openclaw-post = {
            type = "app";
            program = "${openclaw-post}/bin/openclaw-post";
          };
        };
        
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            nodejs
            python3
            curl
          ];
          
          shellHook = ''
            echo "╔════════════════════════════════════════════════════════════╗"
            echo "║     OPENCLAW IMPURE CONTAINMENT ENVIRONMENT                ║"
            echo "╚════════════════════════════════════════════════════════════╝"
            echo ""
            echo "Run: nix run .#openclaw-post"
          '';
        };
      }
    );
}
