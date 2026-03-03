{
  description = "5/10: Galois Tower - 71 Layers of Reflection";

  inputs = {
    monster = { url = "path:./04-monster.nix"; flake = false; };
  };

  outputs = { self, monster }:
    let
      monsterData = import monster;
      shards = monsterData.monster.arms.nullstellensatz.shards;
      
      # Generate Galois field tower
      generateLayer = i: {
        layer = i;
        field = "GF(2^${toString (i + 1)})";
        degree = i + 1;
        
        # Reflection: fold through Hecke operators
        reflection = builtins.foldl' 
          (acc: prime: (acc * prime) % 196883)
          (i + 1)
          [ 2 3 5 7 11 13 17 19 23 29 31 41 47 59 71 ];
        
        # Automorphism group
        automorphisms = i + 1;
        
        # Frobenius map: x ↦ x^2
        frobenius_power = 2;
      };
      
    in {
      galois = {
        tower = builtins.genList generateLayer (builtins.fromJSON shards);
        
        base_field = "GF(2)";
        top_field = "GF(2^71)";
        height = builtins.fromJSON shards;
        
        # Tower properties
        properties = {
          is_normal = true;
          is_separable = true;
          is_galois = true;
          characteristic = 2;
        };
      };
    };
}
