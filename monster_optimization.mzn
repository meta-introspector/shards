% Monster Group Optimization
% MiniZinc model for optimal sharding and packing
% AGPL-3.0+ | Commercial: shards@solfunmeme.com

include "globals.mzn";

% Constants
int: n_shards = 71;
int: n_primes = 15;
int: n_bott = 10;
int: monster_dim = 196883;

% 15 Monster primes
array[1..n_primes] of int: monster_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];

% Decision variables
array[1..n_shards] of var 0..1000: shard_load;  % Load per shard
array[1..n_shards] of var 1..n_primes: shard_prime;  % Prime assignment
array[1..n_shards] of var 0..n_bott-1: shard_bott;  % Bott class

% Hecke operator
function var int: hecke(var int: s, var int: p) =
  (p * s + p * p) mod monster_dim;

% Constraints

% 1. Balanced load across shards
constraint forall(i in 1..n_shards-1)(
  abs(shard_load[i] - shard_load[i+1]) <= 50
);

% 2. Each prime used roughly equally
constraint forall(p in 1..n_primes)(
  count(shard_prime, p) >= n_shards div n_primes - 2 /\
  count(shard_prime, p) <= n_shards div n_primes + 2
);

% 3. Bott classes distributed evenly
constraint forall(b in 0..n_bott-1)(
  count(shard_bott, b) >= n_shards div n_bott - 2 /\
  count(shard_bott, b) <= n_shards div n_bott + 2
);

% 4. Cusp (shard 17) gets special treatment
constraint shard_prime[17] = 5;  % Prime 17 (index 7)
constraint shard_bott[17] = 7;   % Bott class 7

% Objective: Minimize variance in shard load
var int: max_load = max(shard_load);
var int: min_load = min(shard_load);
var int: load_variance = max_load - min_load;

solve minimize load_variance;

% Output
output [
  "Monster Group Optimal Sharding\n",
  "================================\n\n",
  "Load variance: \(load_variance)\n",
  "Max load: \(max_load)\n",
  "Min load: \(min_load)\n\n",
  "Cusp (shard 17):\n",
  "  Prime: \(monster_primes[shard_prime[17]])\n",
  "  Bott: \(shard_bott[17])\n",
  "  Load: \(shard_load[17])\n\n",
  "Prime distribution:\n"
] ++
[
  "  Prime \(monster_primes[p]): \(count(shard_prime, p)) shards\n"
  | p in 1..n_primes
] ++
[
  "\nBott distribution:\n"
] ++
[
  "  Class \(b): \(count(shard_bott, b)) shards\n"
  | b in 0..n_bott-1
];
