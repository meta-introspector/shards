% MiniZinc: P2P Gossip Optimization
% Find optimal gossip pattern for 71 peers

include "globals.mzn";

% Parameters
int: num_peers = 71;
int: num_rounds = 10;

% Variables
array[1..num_peers, 1..num_rounds] of var 0..100: state_turn;
array[1..num_peers, 1..num_rounds] of var 0..1000: state_lobsters;

% Initial state (gist loaded)
constraint state_turn[1, 1] = 5;
constraint state_lobsters[1, 1] = 12;

% Other peers start at 0
constraint forall(p in 2..num_peers)(
  state_turn[p, 1] = 0 /\ state_lobsters[p, 1] = 0
);

% Gossip propagation (each round, state spreads)
constraint forall(r in 2..num_rounds)(
  forall(p in 1..num_peers)(
    state_turn[p, r] >= state_turn[p, r-1] /\
    state_lobsters[p, r] >= state_lobsters[p, r-1]
  )
);

% Eventually all peers converge
constraint forall(p in 1..num_peers)(
  state_turn[p, num_rounds] = 5 /\
  state_lobsters[p, num_rounds] = 12
);

% Minimize gossip rounds to convergence
var int: convergence_round;
constraint convergence_round = min([r | r in 1..num_rounds 
  where forall(p in 1..num_peers)(state_turn[p, r] = 5)]);

solve minimize convergence_round;

output [
  "P2P Gossip Convergence:\n",
  "Peers: \(num_peers)\n",
  "Convergence Round: \(convergence_round)\n",
  "Final State: Turn=5, Lobsters=12\n",
  "QED 🔮⚡\n"
];
