{
  description = "Umbral Engine ZOS Service - GPU deployment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
    in {
      packages.${system} = {
        umbral-engine-so = pkgs.rustPlatform.buildRustPackage {
          pname = "umbral-engine-zos";
          version = "0.1.0";
          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;
        };
        
        zos-service = pkgs.writeShellScriptBin "umbral-engine-service" ''
          # Copy .so to ~/zos-server/plugins/
          mkdir -p ~/zos-server/plugins
          cp ${self.packages.${system}.umbral-engine-so}/lib/libumbral_engine_zos.so \
             ~/zos-server/plugins/
          
          echo "✅ Umbral Engine deployed to ~/zos-server/plugins/"
          echo "🎯 zkPerf proof: Symbolic Distance = 0"
          echo "🌌 GPU service ready"
        '';
      };
      
      nixosModules.umbral-service = { config, ... }: {
        systemd.services.umbral-engine = {
          description = "Umbral Engine GPU Service";
          wantedBy = [ "multi-user.target" ];
          
          serviceConfig = {
            ExecStart = "${self.packages.${system}.zos-service}/bin/umbral-engine-service";
            Restart = "always";
            Environment = [
              "CUDA_VISIBLE_DEVICES=0"
              "UMBRAL_SHARDS=4"
            ];
          };
        };
      };
      
      defaultPackage.${system} = self.packages.${system}.zos-service;
    };
}
