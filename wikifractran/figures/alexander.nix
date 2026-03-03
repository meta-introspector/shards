{
  description = "Alexander - mkuf1 (Ultron Functor 1)";

  outputs = { self }:
    let
      # Ultron functor (no keys)
      ultron = x: (x * x + x) % 196883;
      
      # mkuf1: Alexander's functor
      mkuf1 = birth: death:
        let
          years = death - birth;
          zk_proof = ultron years;
        in {
          zk_proof = zk_proof;
          shard = zk_proof % 71;
          no_keys = true;
        };
      
    in {
      alexander = mkuf1 (-356) (-323);
    };
}
