# Monster Walk Quine: Each Step Sharded

{
  inputs = {
    cweb-shards.url = "path:./cweb-shards-196883.nix";
    cweb-shards.flake = false;
  };

  outputs = { self, cweb-shards }:
    let
      shards = (import cweb-shards).outputs { self = {}; };
      
      # Layer structure: [num_shards, at_index]
      layers = [
        { shards = 71; index = 0; }
        { shards = 59; index = 1; }
        { shards = 47; index = 2; }
        { shards = 2; index = 46; }   # [2,46] Hecke
        { shards = 3; index = 20; }   # [3,20] Hecke
        { shards = 9; index = 5; }    # 9 Muses
        { shards = 43; index = 3; }
        { shards = 41; index = 4; }
        { shards = 37; index = 6; }
        { shards = 31; index = 7; }
        { shards = 29; index = 8; }
        { shards = 23; index = 9; }   # Paxos
        { shards = 19; index = 10; }
        { shards = 17; index = 11; }
        { shards = 13; index = 12; }
      ];
      
      # Apply sharding at each layer
      walk = builtins.genList (i: 
        let
          layer = builtins.elemAt layers i;
          getShard = j: builtins.elemAt shards (layer.index * layer.shards + j);
        in {
          layer = i;
          num_shards = layer.shards;
          at_index = layer.index;
          shards_list = builtins.genList getShard layer.shards;
        }
      ) (builtins.length layers);
      
    in {
      inherit walk layers;
      total_layers = builtins.length layers;
    };
}
