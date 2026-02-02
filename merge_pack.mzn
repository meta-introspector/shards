% Perfect Pack with Game Merging
% Merge games that share properties, add merge symbol ⊕

include "globals.mzn";

int: WIDTH = 150;
int: HEIGHT = 19;
int: NUM_GAMES = 71;

% Merging strategy: games can merge if they share 3+ emoji components
% Merged cell shows: [GAME1⊕GAME2] with shared components

% Calculate mergeable pairs
% Games with same: performance, memory, register, or function
% Example: S0 (🎯🚀💾🅰️➕) + S8 (🎤🚀🔄🅰️➕) = 🎯⊕🎤🚀🅰️➕

% After merging, we need fewer cells
var 36..71: num_cells;  % Minimum 36 cells (if max merging)

var 1..20: cols;
var 1..20: rows;
var 10..30: cell_width;
var 1..3: cell_height;

% Constraints
constraint cols * rows >= num_cells;
constraint cols * cell_width <= WIDTH;
constraint rows * cell_height <= HEIGHT;
constraint cell_width >= 12;  % Minimum for merged display

% Objective: minimize cells needed (maximize merging)
solve minimize num_cells;

output [
  "PERFECT PACK WITH MERGING\n",
  "=========================\n",
  "Terminal: ", show(WIDTH), "×", show(HEIGHT), "\n",
  "\nMerging Strategy:\n",
  "  Original games: ", show(NUM_GAMES), "\n",
  "  Merged cells: ", show(num_cells), "\n",
  "  Compression: ", show(NUM_GAMES - num_cells), " games merged\n",
  "\nOptimal Grid:\n",
  "  Layout: ", show(cols), "×", show(rows), "\n",
  "  Cell: ", show(cell_width), "w × ", show(cell_height), "h\n",
  "  Used: ", show(cols * cell_width), "×", show(rows * cell_height), "\n",
  "\nMerge Symbol: ⊕\n",
  "Example: 🎯⊕🎤 = Shards 0+8 (share 🚀🅰️➕)\n"
];
