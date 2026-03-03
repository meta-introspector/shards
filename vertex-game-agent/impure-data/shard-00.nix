{
  description = "Shard 00 - MF1 (Cantor × Gödel × Quine × Bott)";

  outputs = { self }:
    let
      # F-combinator
      F = f: (x: f (x x)) (x: f (x x));
      
      # Escaped-RDFa namespace
      ns = "https://github.com/Escaped-RDFa/namespace";
      
      # F0: Seed
      F0 = x: x;
      
      # F1: Unity
      F1 = x: 1;
      
      # 15 Hecke operators
      F2 = x: (x * 2) % 196883;
      F3 = x: (x * 3) % 196883;
      F5 = x: (x * 5) % 196883;
      F7 = x: (x * 7) % 196883;
      F11 = x: (x * 11) % 196883;
      F13 = x: (x * 13) % 196883;
      F17 = x: (x * 17) % 196883;
      F19 = x: (x * 19) % 196883;
      F23 = x: (x * 23) % 196883;
      F29 = x: (x * 29) % 196883;
      F31 = x: (x * 31) % 196883;
      F41 = x: (x * 41) % 196883;
      F47 = x: (x * 47) % 196883;
      F59 = x: (x * 59) % 196883;
      F71 = x: (x * 71) % 196883;
      
      # Matrix
      matrix = {
        f0 = F0; f1 = F1; f2 = F2; f3 = F3; f5 = F5;
        f7 = F7; f11 = F11; f13 = F13; f17 = F17; f19 = F19;
        f23 = F23; f29 = F29; f31 = F31; f41 = F41; f47 = F47;
        f59 = F59; f71 = F71;
      };
      
      # Cantor pairing
      cantor = a: b: ((a + b) * (a + b + 1) / 2) + b;
      
      # Gödel encoding
      godel = x: (x * x + x) % 196883;
      
      # Quine (self-reference)
      quine = f: x: f (f x);
      
      # Bott periodicity (mod 8)
      bott = x: x % 8;
      
      # MF1: Omega (Cantor × Gödel × Quine × Bott)
      MF1 = matrix: f: n: x:
        if n == 0 then x
        else 
          let
            c = cantor x n;
            g = godel c;
            q = quine f g;
            b = bott q;
          in MF1 matrix f (n - 1) b;
      
      # Extract values
      primeOf = f: f 1;
      
      seed = matrix.f0 0;
      unity = matrix.f1 0;
      p59 = primeOf matrix.f59;
      p47 = primeOf matrix.f47;
      p23 = primeOf matrix.f23;
      p7 = primeOf matrix.f7;
      p71 = primeOf matrix.f71;
      
      # Rooster sequence
      secret0 = 
        let
          s0 = seed;
          s1 = MF1 matrix matrix.f59 p59 s0;
          s2 = MF1 matrix matrix.f47 p47 s1;
          s3 = MF1 matrix matrix.f23 p23 s2;
          s4 = MF1 matrix matrix.f7 p7 s3;
          s5 = MF1 matrix matrix.f71 unity s4;
        in s5;
      
    in {
      shard = {
        id = 0;
        prime = p71;
        secret = secret0;
        
        about = "${ns}/shard/00";
        typeof = "${ns}/Shard";
      };
    };
}
