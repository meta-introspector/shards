% Perfect Emoji Wall Packing - CRITICAL
% Terminal: 150 cols × 19 lines (ACTUAL available space)
% 71 games MUST fit perfectly

include "globals.mzn";

% ACTUAL terminal constraints
int: WIDTH = 150;
int: HEIGHT = 19;  % Real available lines

% 71 games (non-negotiable)
int: NUM_GAMES = 71;

% Minimum space per game
% Each emoji = 2 chars, 8 emojis = 16 chars
% + shard label (4 chars) = 20 chars minimum
int: MIN_CELL_WIDTH = 20;
int: MIN_CELL_HEIGHT = 2;  % 1 line emoji + 1 line label

% Decision variables
var 1..30: cols;
var 1..20: rows;
var MIN_CELL_WIDTH..50: cell_width;
var MIN_CELL_HEIGHT..5: cell_height;

% HARD CONSTRAINTS
constraint cols * rows >= NUM_GAMES;  % Must fit all 71
constraint cols * cell_width <= WIDTH;  % Must fit in 150 cols
constraint rows * cell_height <= HEIGHT;  % Must fit in 19 lines
constraint cell_width >= MIN_CELL_WIDTH;  % Minimum readable
constraint cell_height >= MIN_CELL_HEIGHT;  % Minimum readable

% Minimize wasted space
var int: wasted_cells = (cols * rows) - NUM_GAMES;
var int: wasted_width = WIDTH - (cols * cell_width);
var int: wasted_height = HEIGHT - (rows * cell_height);
var int: total_waste = wasted_cells * 100 + wasted_width + wasted_height;

% Maximize utilization
var float: utilization = int2float(NUM_GAMES * cell_width * cell_height) / 
                         int2float(WIDTH * HEIGHT);

solve minimize total_waste;

output [
  "PERFECT PACKING SOLUTION\n",
  "========================\n",
  "Terminal: ", show(WIDTH), "×", show(HEIGHT), " (", show(WIDTH*HEIGHT), " cells)\n",
  "\nGrid Layout:\n",
  "  Columns: ", show(cols), "\n",
  "  Rows: ", show(rows), "\n",
  "  Total cells: ", show(cols * rows), " (", show(wasted_cells), " wasted)\n",
  "\nCell Dimensions:\n",
  "  Width: ", show(cell_width), " chars\n",
  "  Height: ", show(cell_height), " lines\n",
  "\nSpace Usage:\n",
  "  Used width: ", show(cols * cell_width), "/", show(WIDTH), 
    " (", show(wasted_width), " wasted)\n",
  "  Used height: ", show(rows * cell_height), "/", show(HEIGHT), 
    " (", show(wasted_height), " wasted)\n",
  "  Utilization: ", show_float(3, 1, utilization * 100.0), "%\n",
  "\nTotal waste: ", show(total_waste), "\n"
];
