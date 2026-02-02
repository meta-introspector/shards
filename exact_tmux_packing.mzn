% EXACT tmux packing: 150x38 = 5700 chars
% Maximize every bit in 10-fold way

int: W = 150;  % Width
int: H = 38;   % Height
int: TOTAL = W * H;  % 5700 chars

% 10-Fold Way sections
set of int: FOLD = 0..9;

% Decision: chars per fold
array[FOLD] of var 0..TOTAL: chars;

% EXACT constraint: use ALL 5700 chars
constraint sum(f in FOLD)(chars[f]) = TOTAL;

% Minimum per fold (at least 1 line)
constraint forall(f in FOLD)(chars[f] >= W);

% Information density (bits per char)
array[0..9] of int: bits_per_char = array1d(0..9, [
  6,   % 0.REAL: Simple (64 values = 6 bits)
  8,   % 1.COMPLEX: Cusp (256 values = 8 bits)
  7,   % 2.QUATERN: Spacetime (128 = 7 bits)
  6,   % 3.OCTONION: Arrows (64 = 6 bits)
  7,   % 4.CLIFFORD: Symmetry (128 = 7 bits)
  8,   % 5.SPINOR: zkPerf (256 = 8 bits)
  6,   % 6.VECTOR: Coords (64 = 6 bits)
  8,   % 7.TENSOR: Compile (256 = 8 bits)
  3,   % 8.BOTT: Period-8 (8 = 3 bits)
  8    % 9.MONSTER: Complete (256 = 8 bits)
]);

% Importance weight
array[0..9] of int: weight = array1d(0..9, [5, 10, 8, 7, 6, 9, 7, 8, 6, 10]);

% Maximize total bits
var int: total_bits = sum(f in FOLD)(
  (chars[f] div 100) * bits_per_char[f] * weight[f]
);

solve :: int_search(chars, first_fail, indomain_max) maximize total_bits;

output [
  "🌀 EXACT TMUX PACKING (150x38 = 5700 chars)\n",
  "============================================\n",
  "FOLD │ CHARS │ LINES │ BITS │ WEIGHTED\n",
  "─────┼───────┼───────┼──────┼─────────\n"
] ++ [
  show(f) ++ ".   │ " ++ 
  show_int(5, chars[f]) ++ " │ " ++ 
  show_int(5, chars[f] div W) ++ " │ " ++ 
  show_int(4, chars[f] * bits_per_char[f]) ++ " │ " ++
  show_int(7, chars[f] * bits_per_char[f] * weight[f]) ++ "\n"
  | f in FOLD
] ++ [
  "─────┴───────┴───────┴──────┴─────────\n",
  "TOTAL: ", show(sum(f in FOLD)(chars[f])), " chars\n",
  "BITS:  ", show(sum(f in FOLD)(chars[f] * bits_per_char[f])), " bits\n",
  "VALUE: ", show(total_bits), " weighted bits\n",
  "PROOF: ", show(sum(f in FOLD)(chars[f])), " = ", show(TOTAL), " ✓\n",
  "☕🕳️🪟👁️👹🦅🐓🔄🌀⚡\n"
];
