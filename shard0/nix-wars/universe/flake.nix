{
  description = "The Universe: FRACTRAN-generated 71×59×47 space";
  
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  
  outputs = { self, nixpkgs }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      
      # Monster Group primes
      X = 71; Y = 59; Z = 47;
      TOTAL = X * Y * Z;  # 196,883
      
      # FRACTRAN program for universe generation
      fractranProg = [
        { n = 17; d = 91; }   # 17/91
        { n = 78; d = 85; }   # 78/85
        { n = 19; d = 51; }   # 19/51
        { n = 23; d = 38; }   # 23/38
        { n = 29; d = 33; }   # 29/33
        { n = 77; d = 29; }   # 77/29
        { n = 95; d = 23; }   # 95/23
        { n = 77; d = 19; }   # 77/19
        { n = 1; d = 17; }    # 1/17
        { n = 11; d = 13; }   # 11/13
        { n = 13; d = 11; }   # 13/11
        { n = 15; d = 2; }    # 15/2 (halt)
      ];
      
      # Generate slot via FRACTRAN
      genSlot = id: 
        let
          x = id / (Y * Z);
          y = (id / Z) - x * Y;
          z = id - (id / Z) * Z;
          seed = 2 * x * 3 * y * 5 * z;
          hash = builtins.hashString "sha256" (toString seed);
        in {
          inherit id x y z hash;
          fractran_seed = seed;
        };
      
      slots = builtins.genList genSlot TOTAL;
      
      universe = {
        dimensions = { inherit X Y Z TOTAL; };
        fractran = fractranProg;
        slots = slots;
        commitment = builtins.hashString "sha256" (builtins.toJSON slots);
      };
      
    in {
      packages.x86_64-linux = {
        default = pkgs.writeTextDir "universe.json" (builtins.toJSON universe);
        
        compact = pkgs.writeTextDir "universe-compact.json" (builtins.toJSON {
          inherit (universe) dimensions fractran commitment;
          slot_count = builtins.length slots;
        });
      };
      
      lib = {
        inherit universe fractranProg X Y Z TOTAL;
        getSlot = id: builtins.elemAt slots id;
      };
    };
}
