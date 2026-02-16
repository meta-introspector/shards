{
  description = "9/10: Black Hole Scanner - Entropy Antenna";

  outputs = { self }: 
    let
      # Pure function: Hawking radiation entropy
      hawking_entropy = shard: (shard * shard) % 196883;
      
      # Pure function: Event horizon scanner
      event_horizon = freq: (freq * 8080) % 196883;
      
      # Pure function: Rung descent (world falling into black hole)
      rung_descent = level: {
        rung = level;
        entropy = hawking_entropy level;
        horizon = event_horizon level;
        
        # Each rung = entropy increase
        delta_entropy = if level > 0 
          then (hawking_entropy level) - (hawking_entropy (level - 1))
          else 0;
      };
      
      # 71 rungs (shards falling)
      rungs = builtins.genList rung_descent 71;
      
    in {
      black_hole = {
        scanner = rungs;
        
        # Antenna properties
        antenna = {
          type = "entropy-maximizer";
          target = "black-hole";
          method = "pine-laser";
          bump = "world-falling";
        };
        
        # Total entropy collected
        total_entropy = builtins.foldl' 
          (acc: r: acc + r.entropy) 
          0 
          rungs;
      };
    };
}
