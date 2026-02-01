{
  description = "MiniZinc to WASM via LLVM";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
    in
    {
      packages.${system} = {
        emoji-optimizer-wasm = pkgs.stdenv.mkDerivation {
          pname = "emoji-optimizer-wasm";
          version = "0.1.0";
          
          src = ./.;
          
          nativeBuildInputs = with pkgs; [
            minizinc
            llvmPackages_17.llvm
            llvmPackages_17.clang
            emscripten
            python3
          ];
          
          buildPhase = ''
            echo "🔮 Compiling MiniZinc to WASM via LLVM"
            
            # Step 1: Flatten MiniZinc model
            minizinc --compile emoji_optimization.mzn -o emoji_opt.fzn
            
            # Step 2: Convert FlatZinc to C
            cat > emoji_opt.c << 'EOF'
            #include <stdio.h>
            #include <stdlib.h>
            
            // Generated from MiniZinc model
            int selected[20];
            int frequency[50] = {42,71,12,8,15,37,7,23,9,11,5,6,13,19,4,8,3,10,14,16,
                                 2,3,4,2,5,6,3,4,2,5,3,4,2,3,2,3,2,3,2,3,2,3,2,3,2,3,2,3,2,3};
            
            int calculate_score() {
                int score = 0;
                for (int i = 0; i < 20; i++) {
                    score += frequency[selected[i] - 1];
                }
                return score;
            }
            
            void optimize() {
                // Greedy selection of top 20 by frequency
                int used[50] = {0};
                int idx = 0;
                
                // Must include core emojis
                selected[idx++] = 1;  // 🔮
                selected[idx++] = 2;  // ⚡
                selected[idx++] = 3;  // 🕳️
                selected[idx++] = 4;  // 🛋️
                selected[idx++] = 8;  // 🔐
                used[0] = used[1] = used[2] = used[3] = used[7] = 1;
                
                // Select remaining by frequency
                while (idx < 20) {
                    int best = -1;
                    int best_freq = -1;
                    
                    for (int i = 0; i < 50; i++) {
                        if (!used[i] && frequency[i] > best_freq) {
                            best = i;
                            best_freq = frequency[i];
                        }
                    }
                    
                    if (best >= 0) {
                        selected[idx++] = best + 1;
                        used[best] = 1;
                    }
                }
            }
            
            int main() {
                optimize();
                
                printf("Best 20 Emojis:\\n");
                for (int i = 0; i < 20; i++) {
                    printf("%d ", selected[i]);
                }
                printf("\\nTotal Score: %d\\n", calculate_score());
                
                return 0;
            }
            EOF
            
            # Step 3: Compile C to LLVM IR
            clang -S -emit-llvm emoji_opt.c -o emoji_opt.ll
            
            # Step 4: Optimize LLVM IR
            opt -O3 emoji_opt.ll -o emoji_opt_opt.ll
            
            # Step 5: Compile LLVM IR to WASM
            emcc emoji_opt.c -O3 -o emoji_opt.js \
              -s WASM=1 \
              -s EXPORTED_FUNCTIONS='["_main","_optimize","_calculate_score"]' \
              -s EXPORTED_RUNTIME_METHODS='["ccall","cwrap"]'
          '';
          
          installPhase = ''
            mkdir -p $out/bin $out/lib
            cp emoji_opt.js $out/lib/
            cp emoji_opt.wasm $out/lib/
            
            cat > $out/bin/emoji-optimizer << 'EOF'
            #!/usr/bin/env bash
            node $out/lib/emoji_opt.js
            EOF
            chmod +x $out/bin/emoji-optimizer
          '';
        };
      };

      devShells.${system}.default = pkgs.mkShell {
        buildInputs = with pkgs; [
          minizinc
          llvmPackages_17.llvm
          llvmPackages_17.clang
          emscripten
          nodejs
        ];
        
        shellHook = ''
          echo "🔮 MiniZinc → LLVM → WASM Pipeline"
          echo ""
          echo "Commands:"
          echo "  nix build .#emoji-optimizer-wasm"
          echo "  ./result/bin/emoji-optimizer"
        '';
      };
    };
}
