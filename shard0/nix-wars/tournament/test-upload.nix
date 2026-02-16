{
  description = "Test Internet Archive upload with pipelite";
  
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  
  outputs = { self, nixpkgs }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      
      # Test upload script
      testUpload = pkgs.writeShellScriptBin "test-ia-upload" ''
        set -e
        
        echo "🧪 Testing Internet Archive Upload"
        echo "===================================="
        echo ""
        
        # Check for archive
        ARCHIVE=$(ls /tmp/nixwars-tournament-*.tar.gz 2>/dev/null | tail -1)
        
        if [ -z "$ARCHIVE" ]; then
          echo "❌ No archive found. Run create-archive.sh first."
          exit 1
        fi
        
        echo "📦 Archive: $ARCHIVE"
        echo "   Size: $(du -h "$ARCHIVE" | cut -f1)"
        echo ""
        
        # Install internetarchive if needed
        if ! command -v ia &> /dev/null; then
          echo "📦 Installing internetarchive CLI..."
          ${pkgs.python3}/bin/pip3 install --user internetarchive
        fi
        
        # Check for credentials
        if [ -z "$IA_ACCESS_KEY" ] || [ -z "$IA_SECRET_KEY" ]; then
          echo "⚠️  No Internet Archive credentials found"
          echo ""
          echo "To test upload, set:"
          echo "  export IA_ACCESS_KEY=<your_key>"
          echo "  export IA_SECRET_KEY=<your_secret>"
          echo ""
          echo "Get keys from: https://archive.org/account/s3.php"
          echo ""
          echo "🔍 Dry run mode - showing what would be uploaded:"
          echo ""
          
          IDENTIFIER="nixwars-tournament-test-$(date +%Y%m%d-%H%M%S)"
          
          echo "Identifier: $IDENTIFIER"
          echo "File: $ARCHIVE"
          echo "Metadata:"
          echo "  - title: Nix-Wars Tournament - 42 Rounds"
          echo "  - description: Pure functional gaming tournament"
          echo "  - subject: gaming;nix;blockchain;fractran"
          echo "  - date: $(date +%Y-%m-%d)"
          echo ""
          echo "✅ Dry run complete"
          exit 0
        fi
        
        # Real upload
        echo "🚀 Uploading to Internet Archive..."
        echo ""
        
        IDENTIFIER="nixwars-tournament-test-$(date +%Y%m%d-%H%M%S)"
        
        ~/.local/bin/ia upload "$IDENTIFIER" "$ARCHIVE" \
          --metadata="title:Nix-Wars Tournament - 42 Rounds (TEST)" \
          --metadata="description:Pure functional gaming tournament with 18 players" \
          --metadata="subject:gaming;nix;blockchain;fractran;test" \
          --metadata="creator:Nix-Wars Community" \
          --metadata="date:$(date +%Y-%m-%d)" \
          --metadata="language:eng" \
          --metadata="licenseurl:https://www.gnu.org/licenses/agpl-3.0.en.html" \
          --metadata="license:AGPL-3.0 (MIT available for purchase)"
        
        echo ""
        echo "✅ Upload complete!"
        echo "   View at: https://archive.org/details/$IDENTIFIER"
      '';
      
    in {
      packages.x86_64-linux.default = testUpload;
      
      apps.x86_64-linux.default = {
        type = "app";
        program = "${testUpload}/bin/test-ia-upload";
      };
    };
}
