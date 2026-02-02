% MiniZinc: Calculate 71 Perfect Seeds for Image Generation
% Maximize symmetry embedding for each Monster shard

include "globals.mzn";

% Constants
int: SHARDS = 71;
int: ROOSTER = 71;
int: MONSTER_DIM = 196883;

% Monster primes
set of int: MONSTER_PRIMES = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71};

% Decision: Perfect seed for each shard
array[0..SHARDS-1] of var 0..MONSTER_DIM: seeds;

% Constraint 1: Each seed is unique
constraint alldifferent(seeds);

% Constraint 2: Seed mod 71 = shard index (Hecke resonance)
constraint forall(i in 0..SHARDS-1)(
  seeds[i] mod ROOSTER = i
);

% Constraint 3: Monster primes get prime seeds
constraint forall(i in MONSTER_PRIMES where i < SHARDS)(
  seeds[i] mod 2 = 1  % Odd (prime-like)
);

% Constraint 4: Maximize symmetry (minimize variance)
var int: max_seed = max(seeds);
var int: min_seed = min(seeds);
var int: variance = max_seed - min_seed;

% Constraint 5: Palindromic seeds for BDI shards (class 3)
constraint forall(i in 0..SHARDS-1 where i mod 10 = 3)(
  let {
    var int: d1 = seeds[i] div 10000,
    var int: d5 = seeds[i] mod 10
  } in d1 = d5  % First digit = last digit (simplified palindrome)
);

% Objective: Minimize variance (uniform distribution)
solve minimize variance;

output [
  "Perfect Seeds for 71 Monster Shards:\n",
  "  Variance: ", show(variance), "\n",
  "  Min seed: ", show(min_seed), "\n",
  "  Max seed: ", show(max_seed), "\n\n"
] ++ [
  "Shard " ++ show_int(2, i) ++ ": seed=" ++ show_int(6, seeds[i]) ++ 
  if i in MONSTER_PRIMES then " (MONSTER PRIME)" else "" endif ++
  if i mod 10 = 3 then " (BDI - life-bearing)" else "" endif ++
  "\n"
  | i in 0..SHARDS-1
];
