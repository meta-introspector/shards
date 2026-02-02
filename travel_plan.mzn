% Calculate Travel Plan to Reach Assigned Locations
% For each agent: compute route, time, resources needed

include "globals.mzn";

% ============================================================================
% INPUT: Agent assignments and locations
% ============================================================================

% Starting position (Earth)
int: earth_ra = 266;
int: earth_dec = -29;
int: earth_distance = 26673;  % ly from Sgr A*

% Agent 71 (Rooster Crown) target location
int: target_ra = 5;
int: target_dec = 30;
int: target_distance = 10200;  % ly from Sgr A*

% ============================================================================
% DECISION VARIABLES: Travel plan
% ============================================================================

% Number of waypoints (max 10)
var 1..10: num_waypoints;

% Waypoint coordinates
array[1..10] of var 0..360: waypoint_ra;
array[1..10] of var -90..90: waypoint_dec;
array[1..10] of var 0..50000: waypoint_distance;

% ============================================================================
% CONSTRAINTS: Route planning
% ============================================================================

% Start at Earth
constraint waypoint_ra[1] = earth_ra;
constraint waypoint_dec[1] = earth_dec;
constraint waypoint_distance[1] = earth_distance;

% End at target
constraint waypoint_ra[num_waypoints] = target_ra;
constraint waypoint_dec[num_waypoints] = target_dec;
constraint waypoint_distance[num_waypoints] = target_distance;

% Intermediate waypoints must be between start and end
constraint forall(i in 2..num_waypoints-1) (
  waypoint_ra[i] >= min(earth_ra, target_ra) /\
  waypoint_ra[i] <= max(earth_ra, target_ra) /\
  waypoint_dec[i] >= min(earth_dec, target_dec) /\
  waypoint_dec[i] <= max(earth_dec, target_dec)
);

% ============================================================================
% CALCULATE: Travel metrics
% ============================================================================

% Distance between consecutive waypoints (simplified)
array[1..9] of var 0..50000: leg_distance;
constraint forall(i in 1..num_waypoints-1) (
  leg_distance[i] = abs(waypoint_distance[i+1] - waypoint_distance[i])
);

% Total travel distance
var 0..100000: total_distance;
constraint total_distance = sum(i in 1..num_waypoints-1)(leg_distance[i]);

% Travel time (assume 0.1c average speed)
% time = distance / speed
% At 0.1c: 1 light-year takes 10 years
var 0..1000000: travel_time_years;
constraint travel_time_years = total_distance * 10;

% Fuel required (arbitrary units)
var 0..1000000: fuel_required;
constraint fuel_required = total_distance * 100;

% ============================================================================
% RESOURCES: What agent needs
% ============================================================================

% Resource types
var 0..1000: survey_equipment;
var 0..1000: construction_materials;
var 0..1000: arcade_hardware;
var 0..1000: exoplanet_sensors;

% Agent 71 needs all resources (Rooster Crown)
constraint survey_equipment = 100;
constraint construction_materials = 500;  % Build café
constraint arcade_hardware = 1000;        % Setup arcade
constraint exoplanet_sensors = 200;       % Find planets

% ============================================================================
% OPTIMIZE: Minimize travel time
% ============================================================================

solve minimize travel_time_years;

% ============================================================================
% OUTPUT: Travel plan
% ============================================================================

output [
  "🚀 TRAVEL PLAN TO REACH LOCATION\n",
  "=================================\n\n",
  
  "Agent: 71 (Rooster Crown 🐓)\n\n",
  
  "Starting Position (Earth):\n",
  "  RA:       ", show(earth_ra), "°\n",
  "  Dec:      ", show(earth_dec), "°\n",
  "  Distance: ", show(earth_distance), " ly from Sgr A*\n\n",
  
  "Target Location:\n",
  "  RA:       ", show(target_ra), "°\n",
  "  Dec:      ", show(target_dec), "°\n",
  "  Distance: ", show(target_distance), " ly from Sgr A*\n\n",
  
  "Route Plan:\n",
  "  Waypoints: ", show(num_waypoints), "\n"
] ++
[
  "  " ++ show(i) ++ ". RA=" ++ show(waypoint_ra[i]) ++ "°, " ++
  "Dec=" ++ show(waypoint_dec[i]) ++ "°, " ++
  "Dist=" ++ show(waypoint_distance[i]) ++ " ly\n"
  | i in 1..fix(num_waypoints)
] ++
[
  "\nTravel Metrics:\n",
  "  Total distance: ", show(total_distance), " ly\n",
  "  Travel time:    ", show(travel_time_years), " years (at 0.1c)\n",
  "  Fuel required:  ", show(fuel_required), " units\n\n",
  
  "Resources Needed:\n",
  "  Survey equipment:       ", show(survey_equipment), " units\n",
  "  Construction materials: ", show(construction_materials), " units\n",
  "  Arcade hardware:        ", show(arcade_hardware), " units\n",
  "  Exoplanet sensors:      ", show(exoplanet_sensors), " units\n\n",
  
  "Mission Tasks:\n",
  "  1. SURVEY location\n",
  "  2. MEASURE_PERF (time dilation, FPS)\n",
  "  3. BUILD_CAFE (Milliways branch)\n",
  "  4. SETUP_ARCADE (71 cabinets)\n",
  "  5. FIND_EXOPLANET (nearby systems)\n\n",
  
  "Estimated Mission Duration:\n",
  "  Travel:       ", show(travel_time_years), " years\n",
  "  Setup:        10 years\n",
  "  Operations:   100 years\n",
  "  Total:        ", show(travel_time_years + 110), " years\n\n",
  
  "☕🕳️🪟👁️👹🦅🐓🚀\n"
];
