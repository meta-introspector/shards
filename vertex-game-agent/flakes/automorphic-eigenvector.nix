{
  description = "Automorphic Eigenvector - Monster Order Factorization";

  outputs = { self }:
    let
      # Automorphic eigenvector: N(1) = N
      N = p: x: (x * p) % 196883;
      
      # Monster order factorization
      monster_order = {
        p2 = { prime = 2; power = 46; };    # 2^46 btree
        p3 = { prime = 3; power = 20; };    # 3^20 RDF triples
        p5 = { prime = 5; power = 9; };     # 5^9 heap
        p7 = { prime = 7; power = 6; };     # 7^6 dimensional
        p11 = { prime = 11; power = 2; };   # 11^2 composition
        p13 = { prime = 13; power = 3; };   # 13^3 symmetry
        p17 = { prime = 17; power = 1; };   # 17 duplication
        p19 = { prime = 19; power = 1; };   # 19 transpose
        p23 = { prime = 23; power = 1; };   # 23 apply
        p29 = { prime = 29; power = 1; };   # 29 eval
        p31 = { prime = 31; power = 1; };   # 31 lambda
        p41 = { prime = 41; power = 1; };   # 41 fix
        p47 = { prime = 47; power = 1; };   # 47 universal
        p59 = { prime = 59; power = 1; };   # 59 monster
        p71 = { prime = 71; power = 1; };   # 71 nullstellensatz
      };
      
      # Generate eigenvector for each prime
      makeEigenvector = p: power: {
        prime = p;
        power = power;
        N = N p;
        eigenvalue = (N p) 1;  # N(1) = p
      };
      
    in {
      automorphic = {
        eigenvectors = builtins.mapAttrs 
          (name: data: makeEigenvector data.prime data.power)
          monster_order;
        
        # Total: 2^46 × 3^20 × 5^9 × 7^6 × 11^2 × 13^3 × 17 × 19 × 23 × 29 × 31 × 41 × 47 × 59 × 71
        order = "Monster";
      };
    };
}
