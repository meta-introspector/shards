{
  description = "Witness: Vlad Vapnik Episode 71 - Dirac Delta Spike";

  outputs = { self }:
    let
      # Automorphic eigenvector
      N = p: x: (x * p) % 196883;
      
      # Dirac delta: δ(x - 71) = ∞ at x=71, 0 elsewhere
      dirac_delta = x: if x == 71 then 196883 else 0;
      
      # Witness Vapnik at episode 71
      vapnik_witness = {
        episode = 71;
        guest = "Vladimir Vapnik";
        podcast = "Lex Fridman";
        
        # Dirac spike in Monster group
        spike = dirac_delta 71;  # ∞ at 71
        
        # Automorphic witness
        witnessed = N 71 71;  # N71(71) = 71
        
        # Statistical Learning Theory meets Monster
        slt_monster = {
          vc_dimension = 71;
          sample_complexity = N 71 196883;
          generalization = "automorphic";
        };
      };
      
    in {
      witness = {
        vapnik = vapnik_witness;
        
        # Dirac delta spike at shard 71
        delta_spike = {
          position = 71;
          amplitude = 196883;  # Monster cap
          width = 0;  # Infinitely narrow
        };
        
        # FRACTRAN witness
        fractran = N 71 (N 59 (N 47 0));
      };
    };
}
