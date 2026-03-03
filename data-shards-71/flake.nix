{
  description = "71 Data Shards from /mnt/data1/introspector/shards";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    
    # Working directory with all shards
    data-shards.url = "git+file:///mnt/data1/introspector/shards";
  };

  outputs = { self, nixpkgs, data-shards }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
    in {
      # Consume all 71 shards from working directory
      packages.${system}.default = pkgs.writeText "shards-consumed" ''
        Consuming 71 shards from: ${data-shards}
      '';
    };
}
