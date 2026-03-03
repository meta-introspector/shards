{
  description = "FRACTRAN meta-macro file sharding";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    fractran-constants.url = "git+file:///home/mdupont/projects/cicadia71/shards?dir=.";
    data-shards-71.url = "git+file:///home/mdupont/projects/cicadia71/shards?dir=data-shards-71";
  };

  outputs = { self, nixpkgs, fractran-constants, data-shards-71 }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
      
      fc = fractran-constants.outputs.shards or [];
      
      prime_71 = builtins.elemAt (builtins.elemAt fc 0) 0;
      
    in {
      packages.${system}.default = pkgs.rustPlatform.buildRustPackage {
        pname = "shard-files-monster";
        version = "0.1.0";
        src = ./.;
        cargoLock.lockFile = ./Cargo.lock;
      };
      
      packages.${system}.shard-runner = pkgs.writeShellScriptBin "shard-files" ''
        export INPUT_FILE=/mnt/data1/files.txt
        export OUTPUT_FILE=files_monster_shards.json
        export SHARD_PRIME=${toString prime_71}
        ${self.packages.${system}.default}/bin/shard-files-monster
      '';
    };
}
