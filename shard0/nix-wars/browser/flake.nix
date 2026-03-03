{
  description = "Nix-Wars Browser Game Engine";
  
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    universe.url = "path:../universe";
  };
  
  outputs = { self, nixpkgs, universe }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      
      gameEngine = pkgs.writeTextFile {
        name = "nix-wars-engine.js";
        text = ''
          // Nix-Wars Browser Game Engine
          const UNIVERSE = ${builtins.toJSON universe.lib.universe};
          
          class NixWarsEngine {
            constructor(canvas) {
              this.canvas = canvas;
              this.ctx = canvas.getContext('2d');
              this.ship = { x: 0, y: 0, sector: 0, credits: 1000000 };
              this.states = [];
              this.orbits = [];
            }
            
            loadStates(statesJson) {
              this.states = statesJson;
              this.generateOrbits();
            }
            
            generateOrbits() {
              const self = this;
              this.orbits = this.states.map(function(state, i) {
                const commitment = state.zkperf && state.zkperf.commitment ? state.zkperf.commitment : "";
                return {
                  x: Math.cos(i * 0.628) * (200 + state.round * 50),
                  y: Math.sin(i * 0.628) * (200 + state.round * 50),
                  state: state,
                  emoji: self.commitmentToEmoji(commitment),
                  radius: 20
                };
              });
            }
            
            commitmentToEmoji(commitment) {
              const map = {
                '0':'🌑','1':'🌒','2':'🌓','3':'🌔','4':'🌕','5':'🌖',
                '6':'🌗','7':'🌘','8':'⭐','9':'✨','a':'🚀','b':'🛸',
                'c':'🌌','d':'🔮','e':'💫','f':'🌠'
              };
              return commitment.slice(0,8).split("").map(function(c) {
                return map[c] || '❓';
              }).join("");
            }
            
            warp(fromSector, toSector) {
              const commitment = this.hashMove(fromSector, toSector);
              return { commitment, from: fromSector, to: toSector };
            }
            
            hashMove(from, to) {
              const data = JSON.stringify({ from, to, timestamp: Date.now() });
              return this.sha256(data).slice(0, 16);
            }
            
            sha256(str) {
              // Simplified hash for browser
              let hash = 0;
              for (let i = 0; i < str.length; i++) {
                hash = ((hash << 5) - hash) + str.charCodeAt(i);
                hash = hash & hash;
              }
              return Math.abs(hash).toString(16).padStart(16, '0');
            }
            
            render() {
              this.ctx.fillStyle = '#000';
              this.ctx.fillRect(0, 0, this.canvas.width, this.canvas.height);
              
              // Draw orbits
              this.orbits.forEach(orbit => {
                this.ctx.fillStyle = '#0f0';
                this.ctx.beginPath();
                this.ctx.arc(
                  this.canvas.width/2 + orbit.x,
                  this.canvas.height/2 + orbit.y,
                  orbit.radius, 0, Math.PI * 2
                );
                this.ctx.fill();
                
                this.ctx.font = '20px monospace';
                this.ctx.fillText(
                  orbit.emoji,
                  this.canvas.width/2 + orbit.x - 40,
                  this.canvas.height/2 + orbit.y - 30
                );
              });
              
              // Draw ship
              this.ctx.fillStyle = '#ff0';
              this.ctx.font = '24px monospace';
              this.ctx.fillText('🚀', 
                this.canvas.width/2 + this.ship.x,
                this.canvas.height/2 + this.ship.y
              );
            }
            
            update(dt) {
              // Game loop
              this.render();
            }
          }
          
          window.NixWarsEngine = NixWarsEngine;
        '';
      };
      
      indexHtml = pkgs.writeTextFile {
        name = "index.html";
        text = ''
          <!DOCTYPE html>
          <html>
          <head>
            <title>Nix-Wars</title>
            <style>
              body { margin: 0; background: #000; overflow: hidden; }
              canvas { display: block; }
              #hud {
                position: absolute;
                top: 20px;
                left: 20px;
                color: #0f0;
                font-family: monospace;
                background: rgba(0,0,0,0.8);
                padding: 15px;
                border: 2px solid #0ff;
              }
            </style>
          </head>
          <body>
            <canvas id="game"></canvas>
            <div id="hud">
              <h3>🚀 NIX-WARS</h3>
              <div>Sector: <span id="sector">0</span></div>
              <div>Credits: <span id="credits">1000000</span></div>
              <div>States: <span id="states">0</span></div>
            </div>
            <script src="nix-wars-engine.js"></script>
            <script>
              const canvas = document.getElementById('game');
              canvas.width = window.innerWidth;
              canvas.height = window.innerHeight;
              
              const engine = new NixWarsEngine(canvas);
              
              fetch('nix-wars-orbits.json')
                .then(r => r.json())
                .then(states => {
                  engine.loadStates(states);
                  document.getElementById('states').textContent = states.length;
                });
              
              function gameLoop() {
                engine.update(1/60);
                requestAnimationFrame(gameLoop);
              }
              gameLoop();
            </script>
          </body>
          </html>
        '';
      };
      
    in {
      packages.x86_64-linux.default = pkgs.runCommand "nix-wars-browser" {} ''
        mkdir -p $out
        cp ${gameEngine} $out/nix-wars-engine.js
        cp ${indexHtml} $out/index.html
      '';
      
      lib.gameEngine = gameEngine;
    };
}
