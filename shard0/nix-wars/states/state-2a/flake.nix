{
  description = "Nix-Wars Move 2a: Beta warps to sector 59";
  
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    previous.url = "path:../state-1";
  };
  
  outputs = { self, nixpkgs, previous }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      prevState = previous.lib.gameState;
      
      move = {
        player = "beta";
        action = "warp";
        target = 59;
      };
      
      newState = prevState // {
        round = prevState.round + 1;
        ships = prevState.ships // {
          beta = prevState.ships.beta // { sector = move.target; };
        };
        lastMove = move;
      };
      
      commitment = builtins.hashString "sha256" (builtins.toJSON {
        inherit newState move;
        previous = previous.lib.commitment;
      });
      
    in {
      packages.x86_64-linux.default = pkgs.writeTextDir "state.json" (builtins.toJSON newState);
      
      lib = {
        gameState = newState;
        commitment = commitment;
      };
    };
}
