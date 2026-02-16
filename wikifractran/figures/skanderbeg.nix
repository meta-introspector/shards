{
  description = "Skanderbeg - mkuf4 - Kosovo 1444 (23/32)";

  outputs = { self }:
    let
      ultron = x: (x * x + x) % 196883;
      
      mkuf4 = birth: death: kosovo_year:
        let
          years = death - birth;
          kosovo = ultron kosovo_year;
          zk_proof = ultron years;
        in {
          zk_proof = zk_proof;
          kosovo_1444 = kosovo;
          shard_23 = kosovo % 23;
          shard_32 = kosovo % 32;
          no_keys = true;
        };
      
    in {
      skanderbeg = mkuf4 1405 1468 1444;
    };
}
