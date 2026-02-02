% MiniZinc: Monster Loadout Trading System

% Monster primes (as indices)
int: NUM_PRIMES = 15;
set of int: PRIME_IDX = 1..NUM_PRIMES;

% Actual prime values
array[PRIME_IDX] of int: PRIME_VAL = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];

% Flow rates (from analysis)
array[PRIME_IDX] of int: FLOW = [14, 10, 9, 9, 15, 15, 9, 8, 9, 10, 9, 8, 9, 9, 8];

% BDI check (mod 10 = 3)
function bool: is_bdi(int: p) = (p mod 10 = 3);

% Decision variables
array[PRIME_IDX] of var bool: selected;
var int: total_flow;
var bool: has_bdi;
var bool: has_rooster;
var bool: conformant;

% Constraints
constraint total_flow = sum(i in PRIME_IDX)(if selected[i] then FLOW[i] else 0 endif);
constraint has_bdi = exists(i in PRIME_IDX)(selected[i] /\ is_bdi(PRIME_VAL[i]));
constraint has_rooster = selected[15];  % 71 is at index 15
constraint conformant = (has_bdi /\ total_flow >= 10 /\ sum(selected) >= 1);

% Monster conformance requirement
constraint conformant;

% Optimization: maximize flow
solve maximize total_flow;

output [
  "Monster Loadout Trading - Conformant Configuration\n",
  "Selected Primes: ", show([PRIME_VAL[i] | i in PRIME_IDX where fix(selected[i])]), "\n",
  "Total Flow: ", show(total_flow), "M\n",
  "Has BDI: ", show(has_bdi), "\n",
  "Has Rooster: ", show(has_rooster), "\n",
  "Conformant: ", show(conformant), "\n",
  "\nBDI Primes: ", show([PRIME_VAL[i] | i in PRIME_IDX where fix(selected[i]) /\ is_bdi(PRIME_VAL[i])]), "\n",
  "Prime Count: ", show(sum(selected)), "/15\n"
];
