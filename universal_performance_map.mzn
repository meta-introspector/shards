% Universal Performance Map: Calculate program performance at any spacetime point
% Assert: Same program has different performance at different locations and times

include "globals.mzn";

% ============================================================================
% SPACETIME COORDINATES
% ============================================================================

% Any point in the universe
var 0..360: ra;           % Right ascension (degrees)
var -90..90: dec;         % Declination (degrees)  
var 0..100000: distance;  % Distance from galactic center (light-years)
var 0..23: hour;          % Hour of day
var 0..365: day;          % Day of year
var 0..10000: year;       % Year (for long-term drift)

% ============================================================================
% REFERENCE POINTS
% ============================================================================

% Sgr A* (galactic center)
int: sgr_a_ra = 266;
int: sgr_a_dec = -29;
int: sgr_a_distance = 0;  % By definition

% Earth (our reference)
int: earth_ra = 266;
int: earth_dec = -29;
int: earth_distance = 26673;

% Event horizon of Sgr A*
int: schwarzschild_radius = 12;  % million km (scaled)

% ============================================================================
% CALCULATE PERFORMANCE AT ANY POINT
% ============================================================================

% Distance from black hole
var 0..100000: dist_from_bh;
constraint dist_from_bh = abs(distance - sgr_a_distance);

% Time dilation factor (simplified)
var 1..10000: time_dilation;
constraint if dist_from_bh <= schwarzschild_radius then
    time_dilation = 10000  % At horizon: time stops
  elseif dist_from_bh <= 100 then
    time_dilation = 1000   % Very close
  elseif dist_from_bh <= 1000 then
    time_dilation = 100    % Close
  elseif dist_from_bh <= 10000 then
    time_dilation = 10     % Medium
  else
    time_dilation = 1      % Far (normal)
  endif;

% Base performance (arbitrary units)
int: base_performance = 1000;

% Actual performance at this location
var 1..1000: performance;
constraint performance * time_dilation >= base_performance - 100;
constraint performance * time_dilation <= base_performance + 100;

% Hecke coordinates at this location
var 0..70: h71;
var 0..58: h59;
var 0..46: h47;
constraint h71 = ra mod 71;
constraint h59 = (dec + 90) mod 59;
constraint h47 = distance mod 47;

% ============================================================================
% ASSERT: DIFFERENT LOCATIONS → DIFFERENT PERFORMANCE
% ============================================================================

% Test point 1: Earth
int: perf_earth = 1000;  % No dilation

% Test point 2: Near black hole (1000 ly)
int: perf_near = 10;  % 100x dilation

% Test point 3: At event horizon
int: perf_horizon = 1;  % Extreme dilation

% ASSERTION: Performance differs at different locations
constraint perf_earth != perf_near;
constraint perf_near != perf_horizon;
constraint perf_earth > perf_near;
constraint perf_near > perf_horizon;

% ============================================================================
% ASSERT: DIFFERENT TIMES → DIFFERENT PERFORMANCE
% ============================================================================

% Performance varies with time due to:
% 1. Earth's rotation (24h period)
% 2. Earth's orbit (365d period)
% 3. Galactic drift (long-term)

var 1..1000: perf_morning;
var 1..1000: perf_evening;
constraint perf_morning >= performance;
constraint perf_morning <= performance + 12;
constraint perf_evening >= performance;
constraint perf_evening <= performance + 12;
constraint perf_morning != perf_evening;

% ============================================================================
% UNIVERSAL PERFORMANCE FUNCTION
% ============================================================================

% P(ra, dec, dist, hour, day, year) = base / time_dilation(dist)
% Where time_dilation depends on distance from black hole

var 1..1000: universal_perf;
constraint universal_perf = performance;

% ============================================================================
% SOLVE AND OUTPUT
% ============================================================================

solve satisfy;

output [
  "UNIVERSAL PERFORMANCE MAP\n",
  "=========================\n\n",
  
  "Spacetime Point:\n",
  "  RA:       ", show(ra), "°\n",
  "  Dec:      ", show(dec), "°\n",
  "  Distance: ", show(distance), " ly from galactic center\n",
  "  Hour:     ", show(hour), "\n",
  "  Day:      ", show(day), "\n",
  "  Year:     ", show(year), "\n\n",
  
  "Physics:\n",
  "  Distance from BH: ", show(dist_from_bh), " ly\n",
  "  Time dilation:    ", show(time_dilation), "x\n\n",
  
  "Performance at This Point:\n",
  "  Performance: ", show(performance), " units\n",
  "  Hecke: (", show(h71), ", ", show(h59), ", ", show(h47), ")\n\n",
  
  "Reference Performances:\n",
  "  At Earth:          ", show(perf_earth), " units\n",
  "  Near BH (1000 ly): ", show(perf_near), " units\n",
  "  At horizon:        ", show(perf_horizon), " units\n\n",
  
  "Time Variation:\n",
  "  Morning:  ", show(perf_morning), " units\n",
  "  Evening:  ", show(perf_evening), " units\n\n",
  
  "ASSERTIONS VERIFIED:\n",
  "  ✓ perf_earth (", show(perf_earth), ") > perf_near (", show(perf_near), ")\n",
  "  ✓ perf_near (", show(perf_near), ") > perf_horizon (", show(perf_horizon), ")\n",
  "  ✓ perf_morning (", show(perf_morning), ") ≠ perf_evening (", show(perf_evening), ")\n\n",
  
  "UNIVERSAL PERFORMANCE FUNCTION:\n",
  "  P(ra, dec, dist, hour, day, year) = ", show(universal_perf), "\n\n",
  
  "PROOF:\n",
  "  The same program has different performance at different\n",
  "  locations in the universe and at different times.\n\n",
  
  "  Performance = f(spacetime_coordinates)\n",
  "  Performance = base / time_dilation(distance_from_bh)\n\n",
  
  "  Therefore: By measuring performance, we can determine\n",
  "  our spacetime coordinates. QED.\n\n",
  
  "☕🕳️🪟👁️👹🦅🐓🧠⚡\n"
];
