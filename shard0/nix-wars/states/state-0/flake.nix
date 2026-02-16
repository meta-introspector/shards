{
  description = "Nix-Wars: TradeWars Genesis State";
  
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  
  outputs = { self, nixpkgs }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      
      state = {
        round = 0;
        timestamp = "2026-02-15T04:37:58Z";
        ships = {
          alpha = { sector = 0; credits = 1000000; };
          beta = { sector = 1; credits = 1000000; };
          gamma = { sector = 2; credits = 1000000; };
        };
      };
      
      commitment = builtins.hashString "sha256" (builtins.toJSON state);
      
    in {
      packages.x86_64-linux.default = pkgs.writeTextDir "state.json" (builtins.toJSON state);
      
      lib = {
        gameState = state;
        commitment = commitment;
      };
    };
}
