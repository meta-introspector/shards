{
  description = "Nix-Wars Move with zkPerf Thermodynamic Witness";
  
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    previous.url = "path:../state-3";
    universe.url = "path:../../universe";
  };
  
  outputs = { self, nixpkgs, previous, universe }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      prevState = previous.lib.gameState;
      
      move = {
        player = "alpha";
        action = "warp";
        from = 42;
        to = 71;
      };
      
      zkperf = {
        commitment = builtins.hashString "sha256" (builtins.toJSON {
          inherit move;
          prev = previous.lib.commitment;
        });
        public_inputs = {
          start_sector = move.from;
          end_sector = move.to;
          universe_commitment = universe.lib.universe.commitment;
        };
      };
      
      newState = prevState // {
        round = prevState.round + 1;
        ships = prevState.ships // {
          alpha = prevState.ships.alpha // { sector = move.to; };
        };
        lastMove = move;
        zkperf = zkperf;
      };
      
      commitment = builtins.hashString "sha256" (builtins.toJSON {
        inherit newState zkperf;
        previous = previous.lib.commitment;
      });
      
    in {
      packages.x86_64-linux.default = pkgs.runCommand "state-4-zkperf" {
        buildInputs = [ pkgs.linuxPackages.perf ];
      } ''
        mkdir -p $out
        
        # Run with perf to generate witness
        perf stat -o $out/perf.txt \
          -e cycles,instructions,cache-misses \
          echo '${builtins.toJSON newState}' > $out/state.json 2>&1 || true
        
        # Store commitment
        echo "${commitment}" > $out/commitment
      '';
      
      lib = {
        gameState = newState;
        commitment = commitment;
        inherit zkperf;
      };
    };
}
