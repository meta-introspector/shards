% Gabulab: Monster Harmonics in MiniZinc
% Optimize shard distribution and harmonic resonances

include "globals.mzn";

% Parameters
int: n_shards = 71;
int: j_coeff = 196884;
int: bott_period = 8;

set of int: MONSTER_PRIMES = {2,3,5,7,11,13,17,19,23,29,31,41,47,59,71};

% Decision variables
array[0..n_shards-1] of var MONSTER_PRIMES: shard_primes;
array[0..n_shards-1] of var 0..j_coeff: j_invariants;
array[0..n_shards-1] of var 0..bott_period-1: bott_periods;

% Constraints

% Each shard has a Bott period
constraint forall(i in 0..n_shards-1)(
  bott_periods[i] = i mod bott_period
);

% j-invariants are well-distributed
constraint forall(i in 0..n_shards-1)(
  j_invariants[i] = (i * 744) mod j_coeff
);

% Primes are cyclic from Monster primes
constraint forall(i in 0..n_shards-1)(
  let {
    int: idx = i mod card(MONSTER_PRIMES)
  } in
  shard_primes[i] in MONSTER_PRIMES
);

% Harmonic resonance: adjacent shards should have related primes
constraint forall(i in 0..n_shards-2)(
  abs(shard_primes[i] - shard_primes[i+1]) <= 20
);

% Topology balance: distribute primes evenly
constraint distribute(
  [count(i in 0..n_shards-1)(shard_primes[i] = p) | p in MONSTER_PRIMES],
  [p | p in MONSTER_PRIMES]
);

% Objective: maximize harmonic resonance
var int: total_resonance = sum(i in 0..n_shards-2)(
  if shard_primes[i] < shard_primes[i+1] then
    shard_primes[i+1] - shard_primes[i]
  else
    shard_primes[i] - shard_primes[i+1]
  endif
);

solve maximize total_resonance;

% Output
output [
  "Gabulab Monster Harmonic Optimization\n",
  "=====================================\n\n"
] ++
[
  "Shard \(i): T_\(shard_primes[i]), j=\(j_invariants[i]), Bott=\(bott_periods[i])\n"
  | i in 0..n_shards-1
] ++
[
  "\nTotal Resonance: \(total_resonance)\n"
];
