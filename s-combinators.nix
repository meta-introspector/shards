# S-Combinator Pure Nix (no number leakage)

let
  # S combinator: S x y z = x z (y z)
  S = x: y: z: (x z) (y z);
  
  # K combinator: K x y = x
  K = x: y: x;
  
  # I combinator: I x = x
  I = x: x;
  
  # Successor: succ n = n + 1
  succ = n: f: x: f (n f x);
  
  # Zero (Church numeral)
  zero = f: x: x;
  
  # Extract from FRACTRAN inputs
  extractOne = shards: 
    let s = builtins.elemAt shards zero;
        frac = builtins.elemAt s (succ (succ (succ zero)));
        pair = builtins.elemAt frac zero;
    in builtins.elemAt pair zero;
  
in {
  inherit S K I succ zero extractOne;
}
