{
  description = "Nix-Wars Move 2b: Gamma warps to sector 71";
  
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    previous.url = "path:../state-1";
  };
  
  outputs = { self, nixpkgs, previous }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      prevState = previous.lib.gameState;
      
      move = {
        player = "gamma";
        action = "warp";
        target = 71;
      };
      
      newState = prevState // {
        round = prevState.round + 1;
        ships = prevState.ships // {
          gamma = prevState.ships.gamma // { sector = move.target; };
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
