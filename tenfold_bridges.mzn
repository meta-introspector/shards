% MiniZinc: Optimal 10-Fold Way Bridge Sizing
% Find optimal palindromic bridges between topological classes

include "globals.mzn";

% 10 topological classes
set of int: TOPO = 0..9;

% Decision variables: find palindromic bridges
var 100..999: nodeA;
var 100..999: nodeB;

% Constraints
constraint nodeA < nodeB;  % Order
constraint nodeA mod 10 != nodeB mod 10;  % Different topo classes

% Palindrome check (simplified for 3-digit numbers)
predicate is_palindrome(var int: n) =
  let {
    var int: d1 = n div 100,
    var int: d2 = (n div 10) mod 10,
    var int: d3 = n mod 10
  } in d1 = d3;

constraint is_palindrome(nodeA);
constraint is_palindrome(nodeB);

% Objective: minimize delta (find smallest bridges)
var int: delta = nodeB - nodeA;

solve minimize delta;

output [
  "Optimal Bridge:\n",
  "  nodeA: ", show(nodeA), " (topo: ", show(nodeA mod 10), ")\n",
  "  nodeB: ", show(nodeB), " (topo: ", show(nodeB mod 10), ")\n",
  "  delta: ", show(delta), "\n",
  "  Palindromes: ", show(is_palindrome(nodeA)), ", ", show(is_palindrome(nodeB)), "\n"
];
