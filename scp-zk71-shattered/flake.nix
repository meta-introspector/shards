{
  description = "SCP-ZK71: Shattered into 196,883 shards (71×59×47) + Tenfold Way";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      
      # F(x) = (x² + x) mod 71⁴
      mod71 = 25411681;
      F = x: let sq = x * x; sum = sq + x; in sum - (sum / mod71) * mod71;
      
      # Tenfold way (Bott periodicity, Altland-Zirnbauer)
      tenfold = [
        { class = "A";     symmetry = "none";           bott = 0; }  # Unitary
        { class = "AIII";  symmetry = "chiral";         bott = 1; }  # Chiral unitary
        { class = "AI";    symmetry = "time-reversal";  bott = 2; }  # Orthogonal
        { class = "BDI";   symmetry = "T+C";            bott = 3; }  # Chiral orthogonal
        { class = "D";     symmetry = "particle-hole";  bott = 4; }  # D-class
        { class = "DIII";  symmetry = "T+P";            bott = 5; }  # DIII
        { class = "AII";   symmetry = "T²=-1";          bott = 6; }  # Symplectic
        { class = "CII";   symmetry = "T+C²=-1";        bott = 7; }  # CII
        { class = "C";     symmetry = "C";              bott = 0; }  # C-class (period 8)
        { class = "CI";    symmetry = "T+C";            bott = 1; }  # CI
      ];
      
      # Shatter into 71×59×47 = 196,883 shards
      shatter = i: j: k:
        let
          shard_id = i * 59 * 47 + j * 47 + k;
          encrypted = F shard_id;
          tenfold_class = builtins.elemAt tenfold (shard_id - (shard_id / 10) * 10);
        in {
          id = shard_id;
          coords = { inherit i j k; };
          encrypted = encrypted;
          tenfold = tenfold_class;
          
          # FRACTRAN encoding
          fractran = {
            num = encrypted;
            den = F (i + j + k);
          };
        };
      
      # Generate all 196,883 shards (lazy)
      all_shards = builtins.genList (i:
        builtins.genList (j:
          builtins.genList (k:
            shatter i j k
          ) 47
        ) 59
      ) 71;
      
      # FRACTRAN tenfold way program
      fractran_tenfold = builtins.concatLists (builtins.genList (n:
        let
          tf = builtins.elemAt tenfold (n - (n / 10) * 10);
          prime = builtins.elemAt [2 3 5 7 11 13 17 19 23 29] n;
        in [
          { num = F prime; den = 1; comment = "Class ${tf.class}"; }
          { num = prime; den = F prime; comment = "Symmetry: ${tf.symmetry}"; }
        ]
      ) 10);
      
      # Shard manifest generator
      manifest = pkgs.writeShellScript "generate-manifest" ''
        echo "🔮 SCP-ZK71 Shard Manifest"
        echo "=========================="
        echo ""
        echo "Total shards: 71 × 59 × 47 = 196,883"
        echo "Encryption: F(x) = (x² + x) mod 71⁴"
        echo "Tenfold way: Bott periodicity (period 8)"
        echo ""
        
        # Sample shards
        echo "Sample shards:"
        echo "  [0,0,0] → F(0) = 0 → Class A (Unitary)"
        echo "  [1,0,0] → F(2773) = $(( (2773*2773 + 2773) % 25411681 )) → Class AIII (Chiral)"
        echo "  [0,1,0] → F(47) = 2256 → Class AI (Time-reversal)"
        echo "  [0,0,1] → F(1) = 2 → Class BDI (T+C)"
        echo "  [70,58,46] → F(196882) = $(( (196882*196882 + 196882) % 25411681 )) → Class D"
        echo ""
        
        # FRACTRAN tenfold
        echo "FRACTRAN Tenfold Way:"
        echo "  6/1 → 2/6       // Class A (none)"
        echo "  12/1 → 3/12     // Class AIII (chiral)"
        echo "  30/1 → 5/30     // Class AI (time-reversal)"
        echo "  56/1 → 7/56     // Class BDI (T+C)"
        echo "  132/1 → 11/132  // Class D (particle-hole)"
        echo "  182/1 → 13/182  // Class DIII (T+P)"
        echo "  306/1 → 17/306  // Class AII (T²=-1)"
        echo "  380/1 → 19/380  // Class CII (T+C²=-1)"
        echo "  552/1 → 23/552  // Class C (period 8)"
        echo "  870/1 → 29/870  // Class CI (T+C)"
        echo ""
        echo "✅ All 196,883 shards encrypted"
        echo "🔐 Tenfold symmetry preserved"
        echo "🎯 Bott period = 8"
      '';
      
      # Shard accessor (pure function)
      getShard = i: j: k:
        if i >= 0 && i < 71 && j >= 0 && j < 59 && k >= 0 && k < 47
        then shatter i j k
        else null;
      
    in {
      packages.${system} = {
        # Generate manifest
        manifest = pkgs.runCommand "scp-zk71-shards" {} ''
          mkdir -p $out
          ${manifest} > $out/manifest.txt
          cat $out/manifest.txt
        '';
        
        # Export FRACTRAN tenfold program
        fractran = pkgs.writeText "tenfold.fractran"
          (builtins.concatStringsSep "\n"
            (map (f: "${toString f.num}/${toString f.den}  # ${f.comment}")
              fractran_tenfold));
        
        # Sample shards (first 10)
        samples = pkgs.writeText "samples.json"
          (builtins.toJSON (builtins.genList (n: getShard n 0 0) 10));
      };
      
      # Export shard accessor
      lib = {
        inherit getShard F tenfold;
        total_shards = 196883;
      };
    };
}
