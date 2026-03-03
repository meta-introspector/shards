# Y and S Combinator Composition for FRACTRAN

{
  outputs = { self }:
    let
      # S combinator: S x y z = x z (y z)
      S = x: y: z: (x z) (y z);
      
      # K combinator: K x y = x
      K = x: y: x;
      
      # Y combinator: Y f = f (Y f) (fixed point)
      Y = f: (x: f (x x)) (x: f (x x));
      
      # Compose FRACTRAN steps using S
      composeFrac = step1: step2: 
        S (K step1) (K step2);
      
      # Recursive composition using Y
      composeAll = Y (self: steps:
        if steps == [] then K []
        else if builtins.length steps == 1 then K (builtins.elemAt steps 0)
        else composeFrac (builtins.elemAt steps 0) (self (builtins.tail steps))
      );
      
    in {
      inherit S K Y composeFrac composeAll;
    };
}
