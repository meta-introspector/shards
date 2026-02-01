{
  description = "Locate Gemini impure Nix files and cache results";

  outputs = { self, nixpkgs ? import <nixpkgs> {} }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system} or nixpkgs;
    in
    {
      packages.${system}.default = pkgs.runCommand "gemini-files-cache" {
        buildInputs = [ pkgs.mlocate pkgs.findutils pkgs.gnugrep ];
      } ''
        mkdir -p $out
        
        echo "🔮 Locating Gemini impure Nix files..."
        
        # Locate gemini flake.nix files
        locate "gemini" | grep -E "\.(nix|sh)$" > $out/gemini_nix_files.txt 2>/dev/null || \
        find /home -name "*gemini*" -type f \( -name "*.nix" -o -name "*.sh" \) 2>/dev/null > $out/gemini_nix_files.txt || \
        touch $out/gemini_nix_files.txt
        
        # Count results
        total=$(wc -l < $out/gemini_nix_files.txt)
        
        # Filter for flake.nix specifically
        grep "flake.nix" $out/gemini_nix_files.txt > $out/gemini_flakes.txt || touch $out/gemini_flakes.txt
        flakes=$(wc -l < $out/gemini_flakes.txt)
        
        # Filter for .sh files
        grep "\.sh$" $out/gemini_nix_files.txt > $out/gemini_scripts.txt || touch $out/gemini_scripts.txt
        scripts=$(wc -l < $out/gemini_scripts.txt)
        
        # Create summary
        cat > $out/summary.txt << EOF
🔮⚡ Gemini Impure Nix Files Cache

Generated: $(date)
Total files: $total
Flake.nix files: $flakes
Shell scripts: $scripts

Files cached in: $out/
- gemini_nix_files.txt (all .nix and .sh)
- gemini_flakes.txt (flake.nix only)
- gemini_scripts.txt (.sh only)

This cache is available to all agents!
EOF
        
        cat $out/summary.txt
        
        # Make it easy to source
        echo "export GEMINI_FILES_CACHE=$out" > $out/env.sh
      '';
    };
}
