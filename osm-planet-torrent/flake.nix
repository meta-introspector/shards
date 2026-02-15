{
  description = "OSM/Wikipedia torrent → IPFS → Solana witness";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    sops-nix.url = "github:Mic92/sops-nix";
    fractran-constants.url = "path:../fractran-constants.nix";
    rust-overlay.url = "github:oxalica/rust-overlay";
  };

  outputs = { self, nixpkgs, sops-nix, fractran-constants, rust-overlay }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs {
        inherit system;
        overlays = [ rust-overlay.overlays.default ];
      };
      
      # Security shard: mod 23 (Paxos witness prime)
      securityShard = 23;
      
    in {
      packages.${system} = {
        osm-torrent-client = pkgs.rustPlatform.buildRustPackage {
          pname = "osm-planet-torrent";
          version = "0.1.0";
          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;
        };
      };
      
      # Monadic execution in security shard
      nixosModules.torrent-witness = { config, ... }: {
        imports = [ sops-nix.nixosModules.sops ];
        
        sops = {
          defaultSopsFile = ./secrets/solana-keypair.yaml;
          secrets = {
            "solana/keypair" = {
              # Only accessible in shard 23
              mode = "0400";
              owner = "torrent-witness";
            };
            "ipfs/api-key" = {
              mode = "0400";
              owner = "torrent-witness";
            };
          };
        };
        
        systemd.services.torrent-witness = {
          description = "Torrent → IPFS → Solana witness (shard 23)";
          wantedBy = [ "multi-user.target" ];
          
          serviceConfig = {
            User = "torrent-witness";
            ExecStart = "${self.packages.${system}.osm-torrent-client}/bin/osm-planet-torrent";
            Environment = [
              "SOLANA_KEYPAIR_PATH=${config.sops.secrets."solana/keypair".path}"
              "IPFS_API_KEY_PATH=${config.sops.secrets."ipfs/api-key".path}"
              "SECURITY_SHARD=${toString securityShard}"
            ];
          };
        };
        
        users.users.torrent-witness = {
          isSystemUser = true;
          group = "torrent-witness";
        };
        users.groups.torrent-witness = {};
      };
    };
}
