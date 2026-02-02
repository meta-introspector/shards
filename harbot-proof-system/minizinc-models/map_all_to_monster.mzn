% MiniZinc: Optimize mapping of all data to Monster walk

% Parameters
int: num_data_types = 7;  % Bytes, Trace, Perf, CPU, Reg, Instr, Factor
int: max_data_points = 1000;
int: monster_order_mod = 71;  % Use mod 71 for tractability

% Decision variables
array[1..num_data_types, 1..max_data_points] of var 0..monster_order_mod: data_values;
array[1..num_data_types, 1..max_data_points] of var 0..monster_order_mod: shard_mapping;

% Monster walk step
int: walk_step = 8080;  % 0x1F90

% Constraints

% 1. Each data point maps to a valid shard
constraint forall(t in 1..num_data_types, i in 1..max_data_points) (
    shard_mapping[t, i] = (walk_step * data_values[t, i]) mod monster_order_mod
);

% 2. All shards must be used (coverage)
constraint forall(s in 0..monster_order_mod-1) (
    exists(t in 1..num_data_types, i in 1..max_data_points) (
        shard_mapping[t, i] = s
    )
);

% 3. j-invariant values
array[1..num_data_types, 1..max_data_points] of var 744..14000000: j_values;
constraint forall(t in 1..num_data_types, i in 1..max_data_points) (
    j_values[t, i] = 744 + 196884 * shard_mapping[t, i]
);

% 4. Minimize total walk distance
var int: total_distance = sum(t in 1..num_data_types, i in 1..max_data_points-1) (
    abs(shard_mapping[t, i+1] - shard_mapping[t, i])
);

% 5. Maximize shard diversity
var int: unique_shards = card({shard_mapping[t, i] | t in 1..num_data_types, i in 1..max_data_points});

% Objective: Minimize distance, maximize diversity
solve minimize total_distance - unique_shards * 100;

% Output
output [
    "Monster Walk Optimization:\n",
    "Total distance: ", show(total_distance), "\n",
    "Unique shards: ", show(unique_shards), "\n",
    "Coverage: ", show(unique_shards * 100 div monster_order_mod), "%\n",
    "\nData type mappings:\n"
] ++
[
    "Type ", show(t), " sample shards: ",
    show([shard_mapping[t, i] | i in 1..min(10, max_data_points)]), "\n"
    | t in 1..num_data_types
] ++
[
    "\nj-invariant range: ",
    show(min([j_values[t, i] | t in 1..num_data_types, i in 1..max_data_points])),
    " to ",
    show(max([j_values[t, i] | t in 1..num_data_types, i in 1..max_data_points])),
    "\n"
];
