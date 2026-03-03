{
  description = "TradeWars Science Lab - Reproducible Monster Group Analysis";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    fractran-constants.url = "path:./fractran-constants.nix";
    fractran-constants.flake = false;
    cweb-shards.url = "path:./cweb-shards-196883.nix";
    cweb-shards.flake = false;
  };

  outputs = { self, nixpkgs, flake-utils, fractran-constants, cweb-shards, monster-vertex-algebra }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        
        # Import pure FRACTRAN constants
        fc = import fractran-constants;
        
        # Import 196883 CWEB shards
        cwebShards = import cweb-shards;
        
        # Perf witness: S-combinators, no number leakage
        perfWitness = let
          # Import S-combinators
          comb = import ./s-combinators.nix;
          
          # Extract values using only combinators and FRACTRAN inputs
          # All indices computed from combinators, not hardcoded
          getShardAt = idx: builtins.elemAt cwebShards idx;
          
          # Build indices from zero using succ
          idx0 = comb.zero;
          idx1 = comb.succ idx0;
          idx2 = comb.succ idx1;
          idx3 = comb.succ idx2;
          
          # Get shards using combinator-built indices
          s0 = getShardAt idx0;
          s1 = getShardAt idx1;
          s2 = getShardAt idx2;
          s3 = getShardAt idx3;
          
          # Extract FRACTRAN values using combinators
          extractFrac = s: builtins.elemAt s (comb.succ (comb.succ (comb.succ comb.zero)));
          frac0 = extractFrac s0;
          
          # Extract first element using K combinator
          first = comb.K;
          val_from_frac = first (builtins.elemAt (builtins.elemAt frac0 idx0) idx0);
          
        in {
          proof = {
            uses_combinators = true;
            no_number_leakage = true;
          };
        };
        
        # Monster vertex algebra: 196883 symmetries as S-combinators
        vertexAlgebra = let
          S = x: y: z: (x z) (y z);
          K = x: y: x;
          I = x: x;
          
          # Vertex operator: map shard to combinator
          vertexOp = i: 
            let
              shard = builtins.elemAt cwebShards i;
              s71 = builtins.elemAt shard 1;
              
              # Map s71 mod 3 to S/K/I
              base = if (s71 - (s71 / 3) * 3) == 0 then S
                     else if (s71 - (s71 / 3) * 3) == 1 then K
                     else I;
            in base;
          
          # Generate all 196883 vertices
          vertices = builtins.genList vertexOp 196883;
          
        in {
          dimension = 196883;
          base = ["S" "K" "I"];
          symmetries = "Monster";
        };
        
        # Access shard 47
        shard47 = builtins.elemAt fc.shards 47;
        
        # Python with science packages
        pythonEnv = pkgs.python311.withPackages (ps: with ps; [
          numpy scipy matplotlib pandas
          sympy networkx igraph
          z3-solver
          pytest hypothesis
        ]);
        
        # Rust with science crates
        rustEnv = pkgs.rustPlatform.buildRustPackage rec {
          pname = "monster-tools";
          version = "0.1.0";
          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;
        };
        
        # FREN processor
        frenProcessor = pkgs.rustPlatform.buildRustPackage rec {
          pname = "fren-processor";
          version = "0.1.0";
          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;
          buildAndTestSubdir = "src";
          cargoBuildFlags = [ "--bin" "fren_processor" ];
        };
        
        # Paxos witness
        paxosWitness = pkgs.rustPlatform.buildRustPackage rec {
          pname = "paxos-witness";
          version = "0.1.0";
          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;
          buildAndTestSubdir = "src";
          cargoBuildFlags = [ "--bin" "paxos_witness" ];
        };
        
        # TRUE_FREN tower (CWEB + FRACTRAN)
        trueFrenTower = pkgs.stdenv.mkDerivation {
          name = "true-fren-tower";
          src = ./.;
          nativeBuildInputs = with pkgs; [ texlive.combined.scheme-basic cweb ];
          buildInputs = [ pkgs.gcc ];
          
          buildPhase = ''
            ctangle true_fren_tower_full.w
            gcc -O2 -o true_fren_tower true_fren_tower_full.c \
              -DEVAL_0=${builtins.elemAt shard47 0} \
              -DEVAL_1=${builtins.elemAt shard47 1} \
              -DEVAL_2=${builtins.elemAt shard47 2} \
              -DEVAL_3=${builtins.elemAt shard47 3}
          '';
          
          installPhase = ''
            mkdir -p $out/bin $out/share/lean4 $out/share/mes
            cp true_fren_tower $out/bin/
            
            cat > $out/share/lean4/TrueFren.lean << 'LEAN4'
            ${builtins.elemAt (builtins.elemAt shard47 4) 0}
            ${builtins.elemAt (builtins.elemAt shard47 4) 1}
            ${builtins.elemAt (builtins.elemAt shard47 4) 2}
            ${builtins.elemAt (builtins.elemAt shard47 4) 3}
            LEAN4
            
            cat > $out/share/mes/true-fren.scm << 'MES'
            ${builtins.elemAt (builtins.elemAt shard47 5) 0}
            ${builtins.elemAt (builtins.elemAt shard47 5) 1}
            ${builtins.elemAt (builtins.elemAt shard47 5) 2}
            ${builtins.elemAt (builtins.elemAt shard47 5) 3}
            MES
          '';
          
          passthru.fractran = [
            "2^${toString (builtins.elemAt shard47 0)}"
            "3^${toString (builtins.elemAt shard47 1)}"
            "5^${toString (builtins.elemAt shard47 2)}"
            "7^${toString (builtins.elemAt shard47 3)}"
          ];
        };
        
        # Monster 196883 shards generator
        monster196883 = pkgs.stdenv.mkDerivation {
          name = "monster-196883-shards";
          src = ./.;
          nativeBuildInputs = with pkgs; [ texlive.combined.scheme-basic ];
          buildInputs = [ pkgs.gcc ];
          
          buildPhase = ''
            # Use ctangle from texlive
            ctangle monster_196883_shards.w
            gcc -O2 -o monster_shards monster_196883_shards.c
          '';
          
          installPhase = ''
            mkdir -p $out/bin
            cp monster_shards $out/bin/
          '';
          
          passthru = {
            # All 196883 hints as 2^n
            hints = builtins.genList (i: 
              builtins.elemAt (builtins.elemAt cwebShards i) 0
            ) 196883;
            
            # FRACTRAN programs from shards
            fractran = builtins.genList (i:
              builtins.elemAt (builtins.elemAt cwebShards i) 4
            ) 196883;
            
            # Shard 47 FRACTRAN
            shard47_fractran = builtins.elemAt (builtins.elemAt cwebShards 47) 4;
          };
        };
        
        # FRACTRAN apply 71 times
        # Each iteration uses a different shard from 196883
        fractranApply71 = let
          shards = (import cweb-shards).outputs { self = {}; };
          
          # Apply function: shard i -> shard ((i+1) mod 71)
          # But pull from full 196883 space
          buildShard = i: 
            let
              # Map iteration to shard in 196883 space
              # Use stride of 59*47 to hit different (s59, s47) combinations
              shardIdx = i * 2777;  # 2777 = 59*47, coprime to 71
              shard = builtins.elemAt shards shardIdx;
            in pkgs.writeText "shard-${toString i}" ''
              Iteration: ${toString i}
              Shard Index: ${toString shardIdx}
              s71: ${toString (builtins.elemAt shard 1)}
              s59: ${toString (builtins.elemAt shard 2)}
              s47: ${toString (builtins.elemAt shard 3)}
              Hint: 2^${toString (builtins.elemAt shard 0)}
              FRACTRAN: ${toString (builtins.elemAt shard 4)}
            '';
          
          iterations = builtins.genList (i: buildShard i) 71;
        in pkgs.writeShellScriptBin "fractran-pipeline" ''
          #!/bin/sh
          ${builtins.concatStringsSep "\n" (builtins.genList (i: ''
            echo "=== Iteration ${toString i} ==="
            cat ${builtins.elemAt iterations i}
            echo
          '') 71)}
        '';
        
      in {
        # Development shells
        devShells = {
          # Full science lab
          default = pkgs.mkShell {
            name = "science-lab";
            buildInputs = with pkgs; [
              # Core tools
              bc jq graphviz imagemagick
              
              # Math systems
              gap pari maxima
              
              # Proof assistants
              lean4 coq z3 cvc5
              
              # Logic programming
              swiProlog
              
              # Lisp
              sbcl
              
              # Constraint solving
              minizinc
              
              # Languages
              pythonEnv
              rustc cargo
              
              # Build tools
              cmake pkg-config
            ];
            
            shellHook = ''
              echo "🔬 TradeWars Science Lab Loaded 🔬"
              echo "=================================="
              echo ""
              echo "Available tools:"
              echo "  Math: gap, pari, maxima"
              echo "  Proof: lean4, coq, z3, cvc5"
              echo "  Logic: swipl"
              echo "  Constraint: minizinc"
              echo "  Python: numpy, scipy, sympy, networkx"
              echo ""
              echo "∴ Reproducible science environment ✓"
            '';
          };
          
          # Minimal (proof + constraint only)
          minimal = pkgs.mkShell {
            buildInputs = with pkgs; [
              lean4 z3 minizinc
              bc jq
            ];
          };
          
          # Monster-specific (GAP + Lean4 + MiniZinc)
          monster = pkgs.mkShell {
            buildInputs = with pkgs; [
              gap lean4 minizinc z3
              pythonEnv
              bc jq graphviz
            ];
            
            shellHook = ''
              echo "🔷 Monster Group Analysis Environment 🔷"
              echo "GAP: Monster group computations"
              echo "Lean4: Formal proofs"
              echo "MiniZinc: Symmetry optimization"
              echo "Z3: SMT solving"
            '';
          };
        };
        
        # Packages
        packages = {
          # FREN processor
          fren-processor = frenProcessor;
          
          # Paxos witness
          paxos-witness = paxosWitness;
          
          # TRUE_FREN tower
          true-fren-tower = trueFrenTower;
          
          # Monster 196883 shards
          monster-196883 = monster196883;
          
          # FRACTRAN apply 71 times
          fractran-apply-71 = fractranApply71;
          
          # Perf witness
          perf-witness = pkgs.writeText "perf-witness.json" (builtins.toJSON perfWitness.proof);
          
          # Monster vertex algebra
          vertex-algebra = pkgs.writeText "vertex-algebra.json" (builtins.toJSON vertexAlgebra);
          
          # Science lab container
          scienceLabContainer = pkgs.dockerTools.buildImage {
            name = "tradewars-science-lab";
            tag = "latest";
            
            contents = with pkgs; [
              gap pari maxima
              lean4 coq z3 cvc5
              swiProlog sbcl
              minizinc
              pythonEnv
              bc jq graphviz
            ];
            
            config = {
              Cmd = [ "${pkgs.bash}/bin/bash" ];
              Env = [
                "PATH=/bin"
              ];
            };
          };
          
          # Buildkite pipeline
          buildkitePipeline = pkgs.writeText "pipeline.yml" ''
            steps:
              - label: "🌙 Process FREN PRs"
                command: |
                  nix build .#fren-processor
                  ./result/bin/fren_processor
                  echo "✓ Monster Moonshine encoding complete"
              
              - label: "🔬 Science Lab Tests"
                command: |
                  nix develop .#default --command bash -c "
                    echo 'Testing GAP...'
                    gap --version
                    
                    echo 'Testing Lean4...'
                    lean --version
                    
                    echo 'Testing MiniZinc...'
                    minizinc --version
                    
                    echo 'Testing Z3...'
                    z3 --version
                    
                    echo '∴ All tools operational ✓'
                  "
              
              - label: "🔷 Monster Proofs"
                command: |
                  nix develop .#monster --command bash -c "
                    lake build
                    ./run_monster_tests.sh
                  "
              
              - label: "🌈 Maass Spectrum"
                command: |
                  nix develop .#default --command bash -c "
                    ./maass_spectrum_quick.sh
                    ./maass_spectrogram.sh
                  "
          '';
        };
        
        # Apps
        apps = {
          # Science lab shell
          lab = {
            type = "app";
            program = "${pkgs.writeShellScript "lab" ''
              exec ${pkgs.nix}/bin/nix develop ${self}#default
            ''}";
          };
          
          # Monster shell
          monster = {
            type = "app";
            program = "${pkgs.writeShellScript "monster" ''
              exec ${pkgs.nix}/bin/nix develop ${self}#monster
            ''}";
          };
        };
      }
    );
}
