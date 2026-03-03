{
  description = "Nix-Wars: Immutable Server State with Morphisms";
  
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  
  outputs = { self, nixpkgs }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      
      # Initial server state (genesis)
      genesis = {
        round = 0;
        timestamp = "2026-02-15T07:38:36Z";
        deployment = {
          url = "http://solana.solfunmeme.com:8080";
          commitment = "515c7a960f5260c8";
        };
        players = {};
      };
      
      # Morphism: Player connects
      playerConnect = prevState: player: 
        prevState // {
          round = prevState.round + 1;
          players = prevState.players // {
            ${player} = {
              connected_at = prevState.round + 1;
              sector = 0;
              credits = 1000000;
            };
          };
        };
      
      # Morphism: Player moves
      playerMove = prevState: player: toSector:
        prevState // {
          round = prevState.round + 1;
          players = prevState.players // {
            ${player} = prevState.players.${player} // {
              sector = toSector;
            };
          };
        };
      
      # Compute state commitment
      stateCommitment = state:
        builtins.hashString "sha256" (builtins.toJSON state);
      
      # Example state transitions
      state0 = genesis;
      state1 = playerConnect state0 "alice";
      state2 = playerConnect state1 "bob";
      state3 = playerMove state2 "alice" 42;
      
      # State history
      stateHistory = [
        { round = 0; commitment = stateCommitment state0; }
        { round = 1; commitment = stateCommitment state1; }
        { round = 2; commitment = stateCommitment state2; }
        { round = 3; commitment = stateCommitment state3; }
      ];
      
    in {
      packages.x86_64-linux.default = pkgs.writeTextFile {
        name = "zk-state";
        text = builtins.toJSON {
          genesis_commitment = stateCommitment genesis;
          current_commitment = stateCommitment state3;
          current_state = state3;
          history = stateHistory;
          pure = true;
          immutable = true;
        };
      };
      
      lib = {
        inherit genesis state0 state1 state2 state3;
        inherit playerConnect playerMove stateCommitment;
        inherit stateHistory;
      };
    };
}
