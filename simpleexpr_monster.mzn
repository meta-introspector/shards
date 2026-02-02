% SimpleExpr → Monster Tower via MiniZinc
% Maps Lean4 SimpleExpr constructors to Monster operations

include "globals.mzn";

% 6 SimpleExpr constructors
enum Expr = {BVAR, SORT, CONST, APP, LAM, FORALL};

% 10-fold way
enum Fold = {F0, F1, F2, F3, F4, F5, F6, F7, F8, F9};

% Monster primes (crown primes)
array[Fold] of int: primes = [2, 71, 47, 19, 17, 13, 11, 7, 5, 3];

% Mapping: SimpleExpr → Fold
array[Expr] of var Fold: expr_to_fold;

% Mapping: SimpleExpr → Brainfuck
array[Expr] of string: expr_to_bf = [
  "+><",      % BVAR → cusp
  "++[>+<]",  % SORT → bootstrap
  "[>+<]",    % CONST → spacetime
  ">>+",      % APP → arrows
  "+++[>]",   % LAM → type symmetry
  "++++[>>]"  % FORALL → dependent types
];

% Constraints
constraint expr_to_fold[BVAR] = F1;    % Cusp (GF(71))
constraint expr_to_fold[SORT] = F0;    % Bootstrap (GF(2))
constraint expr_to_fold[CONST] = F2;   % Spacetime (GF(47))
constraint expr_to_fold[APP] = F3;     % Arrows (GF(19))
constraint expr_to_fold[LAM] = F4;     % Type Symmetry (GF(17))
constraint expr_to_fold[FORALL] = F5;  % Dependent Types (GF(13))

% Objective: maximize tower height
var int: tower_height = sum(e in Expr)(primes[expr_to_fold[e]]);

solve maximize tower_height;

output [
  "SimpleExpr → Monster Tower\n",
  "Tower Height: \(tower_height)\n\n"
] ++
[ "  \(e): Fold \(expr_to_fold[e]) (GF(\(primes[expr_to_fold[e]]))) → \(expr_to_bf[e])\n"
  | e in Expr
];
