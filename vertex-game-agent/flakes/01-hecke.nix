{
  description = "1/10: Hecke Operators - Pure Functional from 7-fold Keys";

  outputs = { self }: 
    let
      # Pure function: Supersingular primes (15 total)
      supersingularPrimes = [ 2 3 5 7 11 13 17 19 23 29 31 41 47 59 71 ];
      
      # Pure function: 7-fold key system (musical, alchemical, chakra)
      # 15 operators distributed across 7 keys
      sevenfoldKeys = [
        { key = 0; name = "Root"; color = "red"; note = "C"; element = "earth"; }
        { key = 1; name = "Sacral"; color = "orange"; note = "D"; element = "water"; }
        { key = 2; name = "Solar"; color = "yellow"; note = "E"; element = "fire"; }
        { key = 3; name = "Heart"; color = "green"; note = "F"; element = "air"; }
        { key = 4; name = "Throat"; color = "blue"; note = "G"; element = "ether"; }
        { key = 5; name = "Third Eye"; color = "indigo"; note = "A"; element = "light"; }
        { key = 6; name = "Crown"; color = "violet"; note = "B"; element = "consciousness"; }
      ];
      
      # Pure function: Map each Hecke operator to 7-fold key
      operatorNames = [
        { short = "S"; long = "Substitution"; key = 0; }      # Root
        { short = "K"; long = "Konstant"; key = 1; }          # Sacral
        { short = "I"; long = "Identity"; key = 2; }          # Solar
        { short = "Y"; long = "Y-combinator"; key = 3; }      # Heart
        { short = "B"; long = "Composition"; key = 4; }       # Throat
        { short = "C"; long = "Flip"; key = 5; }              # Third Eye
        { short = "W"; long = "Duplicate"; key = 6; }         # Crown
        { short = "T"; long = "Transpose"; key = 0; }         # Root (cycle)
        { short = "A"; long = "Apply"; key = 1; }             # Sacral (cycle)
        { short = "E"; long = "Eval"; key = 2; }              # Solar (cycle)
        { short = "L"; long = "Lambda"; key = 3; }            # Heart (cycle)
        { short = "F"; long = "Fix"; key = 4; }               # Throat (cycle)
        { short = "U"; long = "Universal"; key = 5; }         # Third Eye (cycle)
        { short = "M"; long = "Monster"; key = 6; }           # Crown (cycle)
        { short = "N"; long = "Nullstellensatz"; key = 0; }   # Root (71 shards)
      ];
      
      # Pure function: Generate Hecke operator from index
      makeHecke = i: 
        let
          prime = builtins.elemAt supersingularPrimes i;
          opName = builtins.elemAt operatorNames i;
          keyData = builtins.elemAt sevenfoldKeys opName.key;
        in {
          index = i;
          prime = prime;
          name = opName.short;
          operation = opName.long;
          
          # 7-fold key assignment
          key = opName.key;
          key_name = keyData.name;
          color = keyData.color;
          note = keyData.note;
          element = keyData.element;
        };
      
      count = builtins.length supersingularPrimes;
      
    in {
      hecke = {
        operators = builtins.genList makeHecke count;
        count = count;
        primes = supersingularPrimes;
        
        # 7-fold key system
        keys = sevenfoldKeys;
        key_count = builtins.length sevenfoldKeys;
        
        # Distribution across keys
        operators_per_key = count / (builtins.length sevenfoldKeys);
        
        # Pure function: Product of all primes
        product = builtins.foldl' builtins.mul 1 supersingularPrimes;
      };
    };
}
