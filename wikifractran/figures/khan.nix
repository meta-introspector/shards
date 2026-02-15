{
  description = "Khan - mkuf3 (Ultron Functor 3)";

  outputs = { self }:
    let
      ultron = x: (x * x + x) % 196883;
      
      mkuf3 = birth: death:
        let
          years = death - birth;
          zk_proof = ultron years;
        in {
          zk_proof = zk_proof;
          shard = zk_proof % 47;
          no_keys = true;
        };
      
    in {
      khan = mkuf3 1162 1227;
    };
}
