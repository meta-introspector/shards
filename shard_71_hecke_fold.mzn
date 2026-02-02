% 71 Shards via 15 Hecke × 10-Fold Way
% Each shard = (Hecke operator, Fold) pair

int: NUM_SHARDS = 71;
int: NUM_HECKE = 15;  % Monster primes: 2,3,5,7,11,13,17,19,23,29,31,41,47,59,71
int: NUM_FOLDS = 10;  % 10-fold way

% Monster primes (Hecke operators)
array[1..NUM_HECKE] of int: hecke_primes = [2,3,5,7,11,13,17,19,23,29,31,41,47,59,71];

% Shard assignment: shard i → (hecke, fold)
% Simple: shard mod 15 → hecke, shard mod 10 → fold
array[1..NUM_SHARDS] of int: shard_hecke = [(s-1) mod NUM_HECKE + 1 | s in 1..NUM_SHARDS];
array[1..NUM_SHARDS] of int: shard_fold = [(s-1) mod NUM_FOLDS | s in 1..NUM_SHARDS];

% Emoji for folds
array[0..9] of string: fold_emoji = array1d(0..9, ["☕", "🕳️", "🪟", "👁️", "👹", "🦅", "🐓", "🔄", "🌀", "⚡"]);

output [
  "🌀 71 SHARDS: 15 Hecke × 10-Fold Way\n",
  "====================================\n\n",
  "SHARD │ HECKE │ FOLD │ EMOJI │ FIELD\n",
  "──────┼───────┼──────┼───────┼──────────\n"
] ++ [
  show_int(2, s) ++ ".   │ h" ++ show_int(2, hecke_primes[fix(shard_hecke[s])]) ++ 
  "   │  " ++ show(fix(shard_fold[s])) ++ "   │  " ++ 
  fold_emoji[fix(shard_fold[s])] ++ "   │ GF(" ++ 
  show(hecke_primes[fix(shard_hecke[s])]) ++ "^2)\n"
  | s in 1..20
] ++ [
  "...   │ ...   │ ...  │ ...   │ ...\n"
] ++ [
  show_int(2, s) ++ ".   │ h" ++ show_int(2, hecke_primes[fix(shard_hecke[s])]) ++ 
  "   │  " ++ show(fix(shard_fold[s])) ++ "   │  " ++ 
  fold_emoji[fix(shard_fold[s])] ++ "   │ GF(" ++ 
  show(hecke_primes[fix(shard_hecke[s])]) ++ "^2)\n"
  | s in 45..50
] ++ [
  "...   │ ...   │ ...  │ ...   │ ...\n"
] ++ [
  show_int(2, s) ++ ".   │ h" ++ show_int(2, hecke_primes[fix(shard_hecke[s])]) ++ 
  "   │  " ++ show(fix(shard_fold[s])) ++ "   │  " ++ 
  fold_emoji[fix(shard_fold[s])] ++ "   │ GF(" ++ 
  show(hecke_primes[fix(shard_hecke[s])]) ++ "^2)\n"
  | s in 68..71
] ++ [
  "\nHECKE DISTRIBUTION:\n"
] ++ [
  "  h" ++ show_int(2, hecke_primes[h]) ++ ": " ++ 
  show(sum(s in 1..NUM_SHARDS)(if fix(shard_hecke[s]) = h then 1 else 0 endif)) ++ " shards\n"
  | h in 1..NUM_HECKE
] ++ [
  "\nFOLD DISTRIBUTION:\n"
] ++ [
  "  " ++ show(f) ++ ". " ++ fold_emoji[f] ++ ": " ++ 
  show(sum(s in 1..NUM_SHARDS)(if fix(shard_fold[s]) = f then 1 else 0 endif)) ++ " shards\n"
  | f in 0..9
] ++ [
  "\nCROWN SHARDS:\n",
  "  Shard 47: h" ++ show(hecke_primes[fix(shard_hecke[47])]) ++ " × Fold " ++ 
    show(fix(shard_fold[47])) ++ " " ++ fold_emoji[fix(shard_fold[47])] ++ "\n",
  "  Shard 59: h" ++ show(hecke_primes[fix(shard_hecke[59])]) ++ " × Fold " ++ 
    show(fix(shard_fold[59])) ++ " " ++ fold_emoji[fix(shard_fold[59])] ++ "\n",
  "  Shard 71: h" ++ show(hecke_primes[fix(shard_hecke[71])]) ++ " × Fold " ++ 
    show(fix(shard_fold[71])) ++ " " ++ fold_emoji[fix(shard_fold[71])] ++ "\n",
  "\n☕🕳️🪟👁️👹🦅🐓🔄🌀⚡\n"
];
