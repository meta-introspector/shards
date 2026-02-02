{
  description = "Lobster Bot Prediction Market - Multi-language implementation";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay.url = "github:oxalica/rust-overlay";
  };

  outputs = { self, nixpkgs, flake-utils, rust-overlay }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs { inherit system overlays; };
        
        rustToolchain = pkgs.rust-bin.stable.latest.default.override {
          extensions = [ "rust-src" ];
          targets = [ "wasm32-unknown-unknown" ];
        };
        
      in {
        packages = {
          # Rust native library
          lobster-market = pkgs.rustPlatform.buildRustPackage {
            pname = "lobster-market";
            version = "0.1.0";
            src = ../lobster-market;
            
            cargoLock = {
              lockFile = ../lobster-market/Cargo.lock;
            };
            
            nativeBuildInputs = [ rustToolchain ];
            
            meta = {
              description = "Lobster Bot Prediction Market (Rust)";
              license = pkgs.lib.licenses.agpl3Plus;
            };
          };
          
          # WASM module
          lobster-wasm = pkgs.rustPlatform.buildRustPackage {
            pname = "lobster-wasm";
            version = "0.1.0";
            src = ../lobster-wasm;
            
            cargoLock = {
              lockFile = ../lobster-wasm/Cargo.lock;
            };
            
            nativeBuildInputs = [ 
              rustToolchain 
              pkgs.wasm-pack
              pkgs.wasm-bindgen-cli
            ];
            
            buildPhase = ''
              wasm-pack build --target web --release
            '';
            
            installPhase = ''
              mkdir -p $out/pkg
              cp -r pkg/* $out/pkg/
            '';
            
            meta = {
              description = "Lobster Bot Prediction Market (WASM)";
              license = pkgs.lib.licenses.agpl3Plus;
            };
          };
          
          # ZOS BBS Door plugin
          lobster-zos-door = pkgs.stdenv.mkDerivation {
            pname = "lobster-zos-door";
            version = "0.1.0";
            
            src = ./.;
            
            nativeBuildInputs = [ 
              rustToolchain
              pkgs.zig
            ];
            
            buildPhase = ''
              # Build Rust library
              cd lobster-market
              cargo build --release
              cd ..
              
              # Create ZOS door wrapper
              cat > lobster_door.zig << 'EOF'
              const std = @import("std");
              
              // ZOS Door API
              const Door = struct {
                  name: []const u8,
                  version: []const u8,
                  author: []const u8,
                  
                  pub fn init() Door {
                      return Door{
                          .name = "Lobster Prediction Market",
                          .version = "0.1.0",
                          .author = "Meta-Introspector",
                      };
                  }
                  
                  pub fn run(self: *Door, user: []const u8) !void {
                      const stdout = std.io.getStdOut().writer();
                      
                      try stdout.print("\x1b[2J\x1b[H", .{});
                      try stdout.print("╔════════════════════════════════════════════════════════════╗\n", .{});
                      try stdout.print("║     LOBSTER BOT PREDICTION MARKET                          ║\n", .{});
                      try stdout.print("║     Monster-Hecke-zkML Framework                           ║\n", .{});
                      try stdout.print("╚════════════════════════════════════════════════════════════╝\n\n", .{});
                      
                      try stdout.print("User: {s}\n\n", .{user});
                      
                      try stdout.print("Market Odds:\n", .{});
                      try stdout.print("  [1] Register: 90%\n", .{});
                      try stdout.print("  [2] Post:     85%\n", .{});
                      try stdout.print("  [3] Comment:  75%\n", .{});
                      try stdout.print("  [4] Lurk:     15%\n\n", .{});
                      
                      try stdout.print("Consensus: Register (90% confidence)\n", .{});
                      try stdout.print("Topological Class: AII (Quantum Spin Hall)\n", .{});
                      try stdout.print("Bott Periodicity: 1 (mod 8)\n\n", .{});
                      
                      try stdout.print("Press any key to continue...", .{});
                      _ = try std.io.getStdIn().reader().readByte();
                  }
              };
              
              pub fn main() !void {
                  var gpa = std.heap.GeneralPurposeAllocator(.{}){};
                  defer _ = gpa.deinit();
                  const allocator = gpa.allocator();
                  
                  const args = try std.process.argsAlloc(allocator);
                  defer std.process.argsFree(allocator, args);
                  
                  const user = if (args.len > 1) args[1] else "Guest";
                  
                  var door = Door.init();
                  try door.run(user);
              }
              EOF
              
              # Compile ZOS door
              zig build-exe lobster_door.zig -O ReleaseFast
            '';
            
            installPhase = ''
              mkdir -p $out/bin
              cp lobster_door $out/bin/
              
              # Create door configuration
              cat > $out/bin/lobster.door << 'EOF'
              [Door]
              Name=Lobster Prediction Market
              Command=lobster_door
              Type=ZOS
              Category=Games
              Description=Monster-Hecke-zkML prediction market for Moltbook agents
              EOF
            '';
            
            meta = {
              description = "Lobster Bot Prediction Market (ZOS BBS Door)";
              license = pkgs.lib.licenses.agpl3Plus;
            };
          };
          
          # Lean4 verification
          lobster-lean = pkgs.stdenv.mkDerivation {
            pname = "lobster-lean";
            version = "0.1.0";
            
            src = ./.;
            
            nativeBuildInputs = [ pkgs.lean4 ];
            
            buildPhase = ''
              lean LobsterMarket.lean
            '';
            
            installPhase = ''
              mkdir -p $out/share
              cp LobsterMarket.lean $out/share/
              cp -r .lake $out/share/ || true
            '';
            
            meta = {
              description = "Lobster Bot Prediction Market (Lean4)";
              license = pkgs.lib.licenses.agpl3Plus;
            };
          };
          
          # MiniZinc model
          lobster-minizinc = pkgs.stdenv.mkDerivation {
            pname = "lobster-minizinc";
            version = "0.1.0";
            
            src = ./.;
            
            nativeBuildInputs = [ pkgs.minizinc ];
            
            buildPhase = ''
              minizinc --compile lobster_market.mzn || true
            '';
            
            installPhase = ''
              mkdir -p $out/share
              cp lobster_market.mzn $out/share/
            '';
            
            meta = {
              description = "Lobster Bot Prediction Market (MiniZinc)";
              license = pkgs.lib.licenses.agpl3Plus;
            };
          };
          
          # Prolog implementation
          lobster-prolog = pkgs.stdenv.mkDerivation {
            pname = "lobster-prolog";
            version = "0.1.0";
            
            src = ./.;
            
            nativeBuildInputs = [ pkgs.swiProlog ];
            
            installPhase = ''
              mkdir -p $out/share
              cp lobster_market.pl $out/share/
            '';
            
            meta = {
              description = "Lobster Bot Prediction Market (Prolog)";
              license = pkgs.lib.licenses.agpl3Plus;
            };
          };
          
          # ZOS plugin
          lobster-zos-plugin = pkgs.rustPlatform.buildRustPackage {
            pname = "lobster-zos-plugin";
            version = "0.1.0";
            src = ../lobster-zos-plugin;
            
            cargoLock = {
              lockFile = ../lobster-zos-plugin/Cargo.lock;
            };
            
            nativeBuildInputs = [ rustToolchain ];
            
            meta = {
              description = "Lobster Bot Prediction Market (ZOS Plugin)";
              license = pkgs.lib.licenses.agpl3Plus;
            };
          };
          
          default = self.packages.${system}.lobster-zos-door;
        };
        
        apps = {
          lobster-door = {
            type = "app";
            program = "${self.packages.${system}.lobster-zos-door}/bin/lobster_door";
          };
          
          default = self.apps.${system}.lobster-door;
        };
        
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            rustToolchain
            wasm-pack
            wasm-bindgen-cli
            zig
            lean4
            minizinc
            swiProlog
            cargo-watch
          ];
          
          shellHook = ''
            echo "╔════════════════════════════════════════════════════════════╗"
            echo "║     Lobster Bot Prediction Market - Dev Environment       ║"
            echo "╚════════════════════════════════════════════════════════════╝"
            echo ""
            echo "Available builds:"
            echo "  nix build .#lobster-market      # Rust native"
            echo "  nix build .#lobster-wasm        # WASM module"
            echo "  nix build .#lobster-zos-door    # ZOS BBS door"
            echo "  nix build .#lobster-lean        # Lean4 verification"
            echo "  nix build .#lobster-minizinc    # MiniZinc model"
            echo "  nix build .#lobster-prolog      # Prolog implementation"
            echo ""
            echo "Run ZOS door:"
            echo "  nix run .#lobster-door"
          '';
        };
      }
    );
}
