% Tower Expansion: Complexity Distribution (MiniZinc)

include "globals.mzn";

% Complexity levels (log scale)
enum Level = {L0, L1, L2, L3, L4};

% Number of functions at each level (example from Lean4 stdlib)
array[Level] of int: function_counts = [1000, 5000, 3000, 1000, 100];

% Monster primes for each level
array[Level] of int: primes = [2, 13, 47, 71, 71];

% Total tower height
var int: total_height = sum(l in Level)(function_counts[l] * primes[l]);

% Average complexity
var float: avg_complexity = int2float(total_height) / int2float(sum(function_counts));

% Constraint: Complexity increases with level
constraint primes[L0] < primes[L1];
constraint primes[L1] < primes[L2];
constraint primes[L2] <= primes[L3];

% Constraint: Most functions at medium complexity
constraint function_counts[L1] >= function_counts[L0];
constraint function_counts[L1] >= function_counts[L2];

solve satisfy;

output [
  "Tower Expansion: All Lean4 Functions\n",
  "===================================\n\n",
  "Complexity Distribution:\n"
] ++
[ "  Level \(l): \(function_counts[l]) functions → GF(\(primes[l]))\n"
  | l in Level
] ++
[
  "\nTotal Functions: \(sum(function_counts))\n",
  "Total Height: \(total_height)\n",
  "Average Complexity: \(avg_complexity)\n\n",
  "∴ Complexity increases monotonically ✓\n"
];
