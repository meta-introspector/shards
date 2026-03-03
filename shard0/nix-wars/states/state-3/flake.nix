{
  description = "Nix-Wars State 3: Consensus Resolution";
  
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    chosen.url = "path:../state-2a";
    rejected.url = "path:../state-2b";
  };
  
  outputs = { self, nixpkgs, chosen, rejected }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      
      consensus = {
        chosen_commitment = chosen.lib.commitment;
        rejected_commitment = rejected.lib.commitment;
        votes = { "2a" = 2; "2b" = 1; };
        quorum = 2;
        winner = "2a";
      };
      
      prevState = chosen.lib.gameState;
      
      newState = prevState // {
        round = prevState.round + 1;
        consensus = consensus;
      };
      
      commitment = builtins.hashString "sha256" (builtins.toJSON {
        inherit newState consensus;
      });
      
    in {
      packages.x86_64-linux.default = pkgs.writeTextDir "state.json" (builtins.toJSON newState);
      
      lib = {
        gameState = newState;
        commitment = commitment;
      };
    };
}
