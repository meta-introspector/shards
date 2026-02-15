{
  description = "Nix-Wars: Immutable Server State with Morphisms";
  
  outputs = { self }:
    let
      # Initial server state (genesis)
      genesis = {
        round = 0;
        timestamp = "2026-02-15T07:38:36Z";
        deployment = {
          url = "http://solana.solfunmeme.com:8080";
          commitment = "515c7a960f5260c8e778521eaac6008f9e867bcbe7fba96813522d56f54e97a6";
        };
        endpoints = {
          "/" = { hash = "db2e92c24224c3c9"; size = 1227; };
          "/bbs.html" = { hash = "d4b006e672876fa3"; size = 1751; };
          "/url-only.html" = { hash = "e32cf92ac61fdb2a"; size = 4939; };
          "/flying-fractran.html" = { hash = "54980fef513f8ad9"; size = 3733; };
          "/nix-wars-orbits.json" = { hash = "4ab662d7b83d2ef1"; size = 1943; };
        };
        players = {};
      };
      
      # Morphism: Player connects
      playerConnect = prevState: player: {
        state = prevState // {
          round = prevState.round + 1;
          players = prevState.players // {
            ${player} = {
              connected_at = prevState.round + 1;
              sector = 0;
              credits = 1000000;
            };
          };
        };
        morphism = {
          type = "player_connect";
          player = player;
          timestamp = "2026-02-15T07:38:36Z";
        };
      };
      
      # Morphism: Player moves
      playerMove = prevState: player: toSector: {
        state = prevState // {
          round = prevState.round + 1;
          players = prevState.players // {
            ${player} = prevState.players.${player} // {
              sector = toSector;
            };
          };
        };
        morphism = {
          type = "player_move";
          player = player;
          from = prevState.players.${player}.sector;
          to = toSector;
          timestamp = "2026-02-15T07:38:36Z";
        };
      };
      
      # Morphism: Deployment update
      deploymentUpdate = prevState: newCommitment: {
        state = prevState // {
          round = prevState.round + 1;
          deployment = prevState.deployment // {
            commitment = newCommitment;
            updated_at = prevState.round + 1;
          };
        };
        morphism = {
          type = "deployment_update";
          old_commitment = prevState.deployment.commitment;
          new_commitment = newCommitment;
          timestamp = "2026-02-15T07:38:36Z";
        };
      };
      
      # Compute state commitment
      stateCommitment = state:
        builtins.hashString "sha256" (builtins.toJSON state);
      
      # Apply morphism (pure function)
      applyMorphism = prevState: morphismFn: args:
        let
          result = morphismFn prevState args;
          newState = result.state;
          commitment = stateCommitment newState;
        in {
          state = newState;
          morphism = result.morphism;
          commitment = commitment;
          previous_commitment = stateCommitment prevState;
        };
      
      # Example state transitions
      state0 = genesis;
      
      state1 = (applyMorphism state0 playerConnect "alice").state;
      
      state2 = (applyMorphism state1 playerConnect "bob").state;
      
      state3 = (applyMorphism state2 
        (s: p: playerMove s p 42) 
        "alice"
      ).state;
      
      # State history (immutable chain)
      stateHistory = [
        { round = 0; state = state0; commitment = stateCommitment state0; }
        { round = 1; state = state1; commitment = stateCommitment state1; }
        { round = 2; state = state2; commitment = stateCommitment state2; }
        { round = 3; state = state3; commitment = stateCommitment state3; }
      ];
      
    in {
      # Export states
      inherit genesis state0 state1 state2 state3 stateHistory;
      
      # Export morphisms
      morphisms = {
        inherit playerConnect playerMove deploymentUpdate;
      };
      
      # Export utilities
      utils = {
        inherit stateCommitment applyMorphism;
      };
      
      # zkState: Proof that state transitions are valid
      zkState = {
        genesis_commitment = stateCommitment genesis;
        current_commitment = stateCommitment state3;
        transitions = builtins.length stateHistory;
        pure = true;
        immutable = true;
        reproducible = true;
      };
    };
}
