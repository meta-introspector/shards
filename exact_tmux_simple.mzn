% EXACT tmux packing: 150x38 = 5700 chars (SIMPLIFIED)

int: W = 150;
int: H = 38;
int: TOTAL = 5700;

% 10 folds, allocate lines (not chars)
array[0..9] of var 1..H: lines;

% EXACT: use all 38 lines
constraint sum(f in 0..9)(lines[f]) = H;

% Bits per line (width * bits_per_char)
array[0..9] of int: bits_per_line = array1d(0..9, [
  900,  % 0: 150 * 6
  1200, % 1: 150 * 8
  1050, % 2: 150 * 7
  900,  % 3: 150 * 6
  1050, % 4: 150 * 7
  1200, % 5: 150 * 8
  900,  % 6: 150 * 6
  1200, % 7: 150 * 8
  450,  % 8: 150 * 3
  1200  % 9: 150 * 8
]);

% Weight
array[0..9] of int: weight = array1d(0..9, [5, 10, 8, 7, 6, 9, 7, 8, 6, 10]);

% Maximize
var int: total_bits = sum(f in 0..9)(
  lines[f] * bits_per_line[f] * weight[f]
);

solve maximize total_bits;

output [
  "🌀 EXACT TMUX PACKING (150x38)\n",
  "===============================\n",
  "FOLD │ LINES │ CHARS │ BITS/L │ TOTAL_BITS\n",
  "─────┼───────┼───────┼────────┼───────────\n"
] ++ [
  show(f) ++ ".   │ " ++ 
  show_int(5, lines[f]) ++ " │ " ++ 
  show_int(5, lines[f] * W) ++ " │ " ++ 
  show_int(6, bits_per_line[f]) ++ " │ " ++
  show_int(9, lines[f] * bits_per_line[f] * weight[f]) ++ "\n"
  | f in 0..9
] ++ [
  "─────┴───────┴───────┴────────┴───────────\n",
  "TOTAL: ", show(sum(f in 0..9)(lines[f])), "/", show(H), " lines ✓\n",
  "CHARS: ", show(sum(f in 0..9)(lines[f] * W)), "/", show(TOTAL), " ✓\n",
  "VALUE: ", show(total_bits), " weighted bits\n",
  "☕🕳️🪟👁️👹🦅🐓🔄🌀⚡\n"
];
