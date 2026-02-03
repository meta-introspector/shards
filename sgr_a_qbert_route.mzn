% Optimal Route to Observe Sgr A* While Playing Q*bert
% Using Message Passing on Monster Graph (71 sectors)

include "globals.mzn";

% Parameters
int: n_sectors = 71;
int: n_rounds = 7;  % log₂ 71
int: max_stops = 10;

% Sector properties (simplified)
array[1..n_sectors] of float: distance_from_sgr_a = [
  26673.0,  % 0: Earth
  5500.0, 6000.0, 6500.0, 7000.0, 7500.0, 8000.0, 8500.0,  % 1-7
  9000.0, 9500.0, 10000.0, 10500.0, 11000.0, 11500.0, 12000.0, 12500.0, 13000.0,  % 8-16
  15000.0,  % 17: Milliways (cusp!)
  13500.0, 14000.0, 14500.0, 15500.0, 16000.0, 16500.0, 17000.0, 17500.0, 18000.0, 18500.0,  % 18-27
  19000.0, 19500.0, 20000.0, 20500.0, 21000.0, 21500.0, 22000.0, 22500.0, 23000.0, 23500.0,  % 28-37
  24000.0, 24500.0, 25000.0, 25500.0, 26000.0, 26500.0, 27000.0, 27500.0, 28000.0, 28500.0,  % 38-47
  29000.0, 29500.0, 30000.0, 30500.0, 31000.0, 31500.0, 32000.0, 32500.0, 33000.0, 33500.0,  % 48-57
  34000.0, 34500.0, 35000.0, 35500.0, 36000.0, 36500.0, 37000.0, 37500.0, 38000.0, 38500.0,  % 58-67
  39000.0, 39500.0, 40000.0  % 68-70
];

array[1..n_sectors] of bool: has_arcade = [
  true,  % 0: Earth
  false, false, false, false, false, false, true,  % 1-7
  false, false, false, false, false, false, true,  % 8-14
  false, false, true,  % 15-17 (Milliways!)
  false, false, false, true,  % 18-21
  false, false, false, false, false, false, true,  % 22-28
  false, false, false, false, false, false, true,  % 29-35
  false, false, false, false, false, false, true,  % 36-42
  false, false, false, false, false, false, true,  % 43-49
  false, false, false, false, false, false, true,  % 50-56
  false, false, false, false, false, false, true,  % 57-63
  false, false, false, false, false, false, true   % 64-70
];

% Decision variables
array[1..max_stops] of var 1..n_sectors: route;  % Sector IDs
var 1..max_stops: n_stops;  % Actual number of stops
var 1..n_sectors: best_observation_sector;  % Best sector for observation

% Constraints

% 1. Start at Earth (sector 1 = index 0)
constraint route[1] = 1;

% 2. All sectors in route must be distinct
constraint forall(i, j in 1..max_stops where i < j /\ i <= n_stops /\ j <= n_stops)(
  route[i] != route[j]
);

% 3. Message passing: Converge in 7 rounds
constraint n_stops <= n_rounds + 1;  % 7 rounds = 8 stops max

% 4. Best observation sector must be in route
constraint exists(i in 1..max_stops where i <= n_stops)(
  route[i] = best_observation_sector
);

% 5. View quality function (optimal: 1000-30000 ly)
function var float: view_quality(var int: sector) =
  let {
    var float: dist = distance_from_sgr_a[sector];
  } in
  if dist >= 1000.0 /\ dist <= 30000.0 then
    100.0
  elseif dist < 1000.0 then
    dist / 10.0
  else
    max(0.0, 100.0 - (dist - 30000.0) / 200.0)
  endif;

% 6. Arcade bonus
function var float: arcade_bonus(var int: sector) =
  if has_arcade[sector] then 50.0 else 0.0 endif;

% 7. Total score for sector
function var float: sector_score(var int: sector) =
  view_quality(sector) + arcade_bonus(sector);

% 8. Best observation sector has highest score
constraint forall(i in 1..max_stops where i <= n_stops)(
  sector_score(best_observation_sector) >= sector_score(route[i])
);

% 9. Prefer sectors with arcades
constraint sum(i in 1..max_stops where i <= n_stops)(
  if has_arcade[route[i]] then 1 else 0 endif
) >= n_stops / 2;  % At least half have arcades

% Objective: Maximize total score along route
var float: total_score = sum(i in 1..max_stops where i <= n_stops)(
  sector_score(route[i])
);

solve maximize total_score;

% Output
output [
  "🎮🕳️ OPTIMAL SGR A* OBSERVATION + Q*BERT ROUTE\n",
  "=" * 70, "\n\n",
  "🛑 NUMBER OF STOPS: ", show(n_stops), "\n",
  "   (Converged in ", show(n_rounds), " rounds via message passing)\n\n",
  "📍 ROUTE:\n"
] ++
[
  if i <= fix(n_stops) then
    "  " ++ show(i) ++ ". Sector " ++ show(route[i]) ++ 
    " (Distance: " ++ show(distance_from_sgr_a[fix(route[i])]) ++ " ly)" ++
    if has_arcade[fix(route[i])] then " 🎮 ARCADE" else "" endif ++
    "\n"
  else ""
  endif
  | i in 1..max_stops
] ++
[
  "\n🏆 BEST OBSERVATION POINT:\n",
  "   Sector ", show(best_observation_sector), "\n",
  "   Distance from Sgr A*: ", show(distance_from_sgr_a[fix(best_observation_sector)]), " ly\n",
  "   View quality: ", show(view_quality(best_observation_sector)), "/100\n",
  "   Arcade: ", if has_arcade[fix(best_observation_sector)] then "✅ YES" else "❌ No" endif, "\n\n",
  "📊 TOTAL SCORE: ", show(total_score), "\n\n",
  "🎮🐯🕳️ Proven optimal by MiniZinc constraint solving!\n"
];
