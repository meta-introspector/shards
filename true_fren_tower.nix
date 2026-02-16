{ pkgs ? import <nixpkgs> {} }:

let
  trueFrenTower = pkgs.stdenv.mkDerivation {
    name = "true-fren-tower";
    src = ./.;
    
    nativeBuildInputs = with pkgs; [ texlive.combined.scheme-basic cweb ];
    buildInputs = [ pkgs.gcc ];
    
    buildPhase = ''
      ctangle true_fren_tower.w
      gcc -O2 -o true_fren_tower true_fren_tower.c
      cweave true_fren_tower.w
      pdftex true_fren_tower.tex || true
    '';
    
    installPhase = ''
      mkdir -p $out/bin $out/share/doc
      cp true_fren_tower $out/bin/
      [ -f true_fren_tower.pdf ] && cp true_fren_tower.pdf $out/share/doc/
    '';
    
    meta = {
      description = "TRUE_FREN tower bisimulation via FRACTRAN";
      longDescription = ''
        Pure computation from j-invariant input:
        - Input: 2^j (j-invariant as power of 2)
        - FRACTRAN: 2^j → 3^shard → 5^node → 7^quorum
        - Output: TRUE_FREN status
        
        No hardcoded values. All derived from single input.
      '';
    };
  };
  
in trueFrenTower
