{
  description = "Data acquisition from /mnt/data1/introspector/shards/data - pure Nix";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    data-shards.url = "git+file:///mnt/data1/introspector/shards";
    fractran-constants.url = "path:../fractran-constants.nix";
  };

  outputs = { self, nixpkgs, data-shards, fractran-constants }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
      
      # Data directory from shards
      dataDir = "${data-shards}/data";
      
    in {
      packages.${system} = {
        # Acquire all data files
        acquire-all = pkgs.writeShellScriptBin "acquire-data" ''
          echo "🔍 Acquiring data from ${dataDir}"
          ${pkgs.ripgrep}/bin/rg --files ${dataDir}
        '';
        
        # Search with new ripgrep
        search-data = pkgs.writeShellScriptBin "search-data" ''
          QUERY="$1"
          echo "🔎 Searching: $QUERY in ${dataDir}"
          ${pkgs.ripgrep}/bin/rg "$QUERY" ${dataDir}
        '';
        
        # Pipe to pipelight
        search2pipe = pkgs.writeShellScriptBin "search2pipe" ''
          QUERY="$1"
          ${pkgs.ripgrep}/bin/rg --json "$QUERY" ${dataDir} | \
            ${pkgs.jq}/bin/jq -c '.'
        '';
      };
      
      defaultPackage.${system} = self.packages.${system}.acquire-all;
    };
}
