% MiniZinc: Calculate Best Emojis from All Inputs
int: num_emojis = 20;
set of int: EMOJIS = 1..50;
array[1..num_emojis] of var EMOJIS: selected;

constraint alldifferent(selected);
constraint member(1, selected);  % 🔮
constraint member(2, selected);  % ⚡
constraint member(3, selected);  % 🕳️
constraint member(4, selected);  % 🛋️
constraint member(8, selected);  % 🔐

array[EMOJIS] of int: frequency = [
  42,71,12,8,15,37,7,23,9,11,5,6,13,19,4,8,3,10,14,16,
  2,3,4,2,5,6,3,4,2,5,3,4,2,3,2,3,2,3,2,3,2,3,2,3,2,3,2,3,2,3
];

var int: total_score = sum(i in 1..num_emojis)(frequency[selected[i]]);
solve maximize total_score;

output ["Score: " ++ show(total_score) ++ "\nEmojis: "] ++ 
       [show(selected[i]) ++ " " | i in 1..num_emojis];
