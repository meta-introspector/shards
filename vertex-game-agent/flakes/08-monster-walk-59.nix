{
  description = "8/10: Monster Walk - 59 Frequency";

  outputs = { self }: 
    let
      # Pure function: 59 Monster Walk
      walk_count = 59;
      frequency = 8080; # Hz
      
      # Pure function: Generate walk step from index
      makeWalkStep = i: {
        id = i;
        step = "walk-${toString i}";
        
        # Pure function: Walk properties
        modulus = walk_count;
        position = i % walk_count;
        
        # Frequency modulation
        freq_offset = (i * frequency) % 196883;
      };
      
    in {
      monster_walk = {
        steps = builtins.genList makeWalkStep walk_count;
        count = walk_count;
        prime = 59;
        frequency = frequency;
        name = "Monster Walk";
      };
    };
}
