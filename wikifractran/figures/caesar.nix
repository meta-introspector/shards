{
  description = "Caesar - mkuf2 (Ultron Functor 2)";

  outputs = { self }:
    let
      ultron = x: (x * x + x) % 196883;
      
      mkuf2 = birth: death:
        let
          years = death - birth;
          zk_proof = ultron years;
        in {
          zk_proof = zk_proof;
          shard = zk_proof % 59;
          no_keys = true;
        };
      
    in {
      caesar = mkuf2 (-100) (-44);
    };
}
