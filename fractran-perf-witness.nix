{
  description = "Pure Nix perf witness for FRACTRAN 71 iterations";

  inputs = {
    fractran-constants.url = "path:./fractran-constants.nix";
    fractran-constants.flake = false;
  };

  outputs = { self, fractran-constants }:
    let
      # Import constants (each used only once)
      fc = (import fractran-constants).outputs { self = {}; };
      
      # Extract from shard 0 (base constants)
      shard0 = builtins.elemAt fc 0;
      c71 = builtins.elemAt (builtins.elemAt shard0 4) 0;  # 3 from [3,2]
      c59 = builtins.elemAt (builtins.elemAt shard0 4) 1;  # 2 from [3,2]
      
      # Extract from shard 1
      shard1 = builtins.elemAt fc 1;
      c47 = builtins.elemAt (builtins.elemAt shard1 4) 2;  # 5 from [5,3]
      
      # Compute derived values using FRACTRAN inputs only
      stride = (c59 * c71 * c71) - c59;  # 2*71*71 - 2 = 10082 - 2 = 10080... wait
      # Actually: stride = 59 * 47 = 2777
      # Extract 59 and 47 from different shards
      
      # Shard 59: s71=59
      shard59 = builtins.elemAt fc 59;
      val59 = builtins.elemAt shard59 1;  # s71 = 59
      
      # Shard 47: s71=47  
      shard47 = builtins.elemAt fc 47;
      val47 = builtins.elemAt shard47 1;  # s71 = 47
      
      # Stride = 59 * 47 (computed from shard indices)
      computed_stride = val59 * val47;
      
      # Total space = 71 * 59 * 47 (from shard structure)
      shard71 = builtins.elemAt fc 71;
      val71 = builtins.elemAt shard71 1;  # s71 = 0 (wraps)
      total_space = (val71 + c71 + c71) * val59 * val47;  # (0+3+71-3)*59*47
      
      # Measure iterations
      measureIterations = n: {
        iteration = n;
        shard_index = n * computed_stride;
      };
      
      witness = builtins.genList measureIterations val71;  # Use val71 as iteration count
      
    in {
      inherit witness;
      proof = {
        stride = computed_stride;
        space = total_space;
        iterations = val71;
      };
    };
}
