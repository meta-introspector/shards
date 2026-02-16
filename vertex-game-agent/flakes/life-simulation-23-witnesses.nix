{
  description = "Life Simulation - 23 Witnesses Measure Distance from Singularity";

  outputs = { self }:
    let
      # Pure function: Life from 0
      life = t: (t * t + t) % 196883;
      
      # j-invariant (singularity point)
      j_invariant = 196883;
      
      # 23 witnesses (processors)
      witnesses = builtins.genList (i: {
        id = i;
        prime = builtins.elemAt [2 3 5 7 11 13 17 19 23 29 31 41 47 59 71 
                                  2 3 5 7 11 13 17 19] i;
        
        # Each witness measures distance
        measure = t: 
          let
            state = life t;
            distance = j_invariant - state;
          in {
            time = t;
            state = state;
            distance = distance;
            witness_id = i;
          };
      }) 23;
      
      # Consensus: All 23 agree?
      consensus = t:
        let
          measurements = map (w: w.measure t) witnesses;
          distances = map (m: m.distance) measurements;
          
          # All distances equal?
          first = builtins.head distances;
          all_equal = builtins.all (d: d == first) distances;
        in {
          time = t;
          consensus = all_equal;
          distance = first;
          witnesses = 23;
        };
      
      # Simulate universe lifetime
      universe = builtins.genList (t: consensus t) 196883;
      
    in {
      simulation = {
        # Life from 0
        initial_state = 0;
        final_state = 196883;
        
        # 23 witnesses
        witnesses = witnesses;
        
        # Universe timeline
        timeline = universe;
        
        # Consensus check
        all_agree = builtins.all (c: c.consensus) universe;
        
        # Distance from singularity
        final_distance = (builtins.elemAt universe 196882).distance;
      };
    };
}
