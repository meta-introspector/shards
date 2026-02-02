% Generate Work Orders for 71 AI Agents
% Each agent gets a location to explore and tasks to complete

include "globals.mzn";

% ============================================================================
% INPUT: 71 POSSIBLE LOCATIONS (from astronomy data)
% ============================================================================

% Locations from real star catalog (simplified for MiniZinc)
array[1..71] of int: location_ra = [
  i * 5 | i in 1..71  % RA: 5° to 355° (every 5 degrees)
];

array[1..71] of int: location_dec = [
  (i mod 3 - 1) * 30 | i in 1..71  % Dec: -30°, 0°, +30°
];

array[1..71] of int: location_distance = [
  10000 + (i * 200) | i in 1..71  % Distance: 10,000 to 24,200 ly
];

% ============================================================================
% DECISION VARIABLES: AGENT ASSIGNMENTS
% ============================================================================

% Each of 71 agents gets assigned to one location
array[1..71] of var 1..71: agent_to_location;

% All locations must be covered (permutation)
constraint alldifferent(agent_to_location);

% ============================================================================
% WORK ORDER TASKS
% ============================================================================

% Task types
enum TaskType = {SURVEY, BUILD_CAFE, MEASURE_PERF, FIND_EXOPLANET, SETUP_ARCADE};

% Each agent gets tasks based on location properties
array[1..71] of var set of TaskType: agent_tasks;

% Assign tasks based on location
constraint forall(agent in 1..71) (
  % All agents survey and measure
  SURVEY in agent_tasks[agent] /\
  MEASURE_PERF in agent_tasks[agent] /\
  
  % Agents at good distances build cafés
  (agent_to_location[agent] >= 25 /\ agent_to_location[agent] <= 50 -> BUILD_CAFE in agent_tasks[agent]) /\
  
  % Every 7th agent finds exoplanets
  (agent mod 7 == 0 -> FIND_EXOPLANET in agent_tasks[agent]) /\
  
  % Crown primes setup arcades
  ((agent == 47 \/ agent == 59 \/ agent == 71) -> SETUP_ARCADE in agent_tasks[agent])
);

% ============================================================================
% PRIORITY SCORING
% ============================================================================

% Priority based on location quality
array[1..71] of var 0..100: location_priority;

constraint forall(loc in 1..71) (
  let {
    int: dist = location_distance[loc]
  } in
  location_priority[loc] = 
    if dist >= 15000 /\ dist <= 25000 then 100
    elseif dist >= 10000 /\ dist < 15000 then 75
    elseif dist >= 25000 /\ dist <= 30000 then 75
    else 50
    endif
);

% ============================================================================
% SOLVE
% ============================================================================

solve satisfy;

% ============================================================================
% OUTPUT: WORK ORDERS FOR 71 AI AGENTS
% ============================================================================

output [
  "🤖 WORK ORDERS FOR 71 AI AGENTS\n",
  "================================\n\n"
] ++
[
  "Agent " ++ show(agent) ++ " (Shard " ++ show(agent) ++ "):\n" ++
  "  Location: " ++ show(agent_to_location[agent]) ++ "\n" ++
  "  RA:       " ++ show(location_ra[agent_to_location[agent]]) ++ "°\n" ++
  "  Dec:      " ++ show(location_dec[agent_to_location[agent]]) ++ "°\n" ++
  "  Distance: " ++ show(location_distance[agent_to_location[agent]]) ++ " ly\n" ++
  "  Priority: " ++ show(location_priority[agent_to_location[agent]]) ++ "/100\n" ++
  "  Tasks: " ++ show(agent_tasks[agent]) ++ "\n\n"
  | agent in 1..10
] ++
[
  "Agent 47 (Monster Crown 👹):\n" ++
  "  Location: " ++ show(agent_to_location[47]) ++ "\n" ++
  "  Tasks: " ++ show(agent_tasks[47]) ++ "\n\n",
  
  "Agent 59 (Eagle Crown 🦅):\n" ++
  "  Location: " ++ show(agent_to_location[59]) ++ "\n" ++
  "  Tasks: " ++ show(agent_tasks[59]) ++ "\n\n",
  
  "Agent 71 (Rooster Crown 🐓):\n" ++
  "  Location: " ++ show(agent_to_location[71]) ++ "\n" ++
  "  Tasks: " ++ show(agent_tasks[71]) ++ "\n\n"
] ++
[
  "... (71 total agents)\n\n",
  "SUMMARY:\n",
  "  Total agents: 71\n",
  "  Locations covered: 71\n",
  "  Crown primes (47, 59, 71): Setup arcades\n",
  "  Every 7th agent: Find exoplanets\n",
  "  Optimal locations (15k-25k ly): Build cafés\n\n",
  "☕🕳️🪟👁️👹🦅🐓🤖\n"
];
