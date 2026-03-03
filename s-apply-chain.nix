# S-Combinator Apply Chain: 5→3→2→1→0

let
  # S combinator: S x y z = x z (y z)
  S = x: y: z: (x z) (y z);
  
  # K combinator: K x y = x
  K = x: y: x;
  
  # I combinator: I x = x
  I = x: x;
  
  # Apply 5: S K K = I
  apply5 = S K K;
  
  # Apply 3: S (K S) K
  apply3 = S (K S) K;
  
  # Apply 2: S apply3
  apply2 = S apply3;
  
  # Apply 1: K S
  apply1 = K S;
  
  # Apply 0: I
  apply0 = I;
  
  # Chain: 5→3→2→1→0
  applyChain = input: 
    apply0 (apply1 (apply2 (apply3 (apply5 input))));
  
in {
  inherit S K I apply5 apply3 apply2 apply1 apply0 applyChain;
}
