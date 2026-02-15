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
        to = 71;  # Omega sector
      };
      
      # zkPerf witness
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
        timestamp = "2026-02-15T05:14:38Z";
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
      packages.x86_64-linux.default = pkgs.writeTextDir "state.json" (builtins.toJSON newState);
      
      lib = {
        gameState = newState;
        commitment = commitment;
        inherit zkperf;
      };
    };
}
