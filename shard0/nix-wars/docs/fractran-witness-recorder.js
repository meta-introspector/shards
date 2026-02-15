// LMFDB Flying Game with FRACTRAN Witness Recorder
// Playing the game generates a FRACTRAN program

class FRACTRANWitnessRecorder {
  constructor() {
    this.program = [];
    this.state = 1; // Initial FRACTRAN state (2^0)
    this.primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];
    this.moves = [];
  }
  
  // Record player position as FRACTRAN state
  recordPosition(x, y, z) {
    // Encode position as 2^x * 3^y * 5^z
    const encoded = Math.pow(2, Math.floor(x/10)) * 
                    Math.pow(3, Math.floor(y/10)) * 
                    Math.pow(5, Math.floor(z/10));
    
    // Generate FRACTRAN fraction to reach this state
    if (this.state !== encoded) {
      const fraction = { n: encoded, d: this.state };
      this.program.push(fraction);
      this.state = encoded;
    }
  }
  
  // Record animation frame as FRACTRAN operation
  recordFrame(frame, velocity) {
    // Encode velocity as prime exponents
    const vx = Math.floor(velocity.x * 10);
    const vy = Math.floor(velocity.y * 10);
    const vz = Math.floor(velocity.z * 10);
    
    this.moves.push({
      frame: frame,
      velocity: { x: vx, y: vy, z: vz },
      state: this.state
    });
  }
  
  // Record sector transition
  recordSectorChange(from, to) {
    // Generate FRACTRAN fraction for sector warp
    const prime_from = this.primes[from % this.primes.length];
    const prime_to = this.primes[to % this.primes.length];
    
    const fraction = { n: prime_to, d: prime_from };
    this.program.push(fraction);
  }
  
  // Export FRACTRAN program
  exportProgram() {
    return {
      program: this.program,
      moves: this.moves,
      initial_state: 1,
      final_state: this.state,
      timestamp: new Date().toISOString()
    };
  }
  
  // Generate Nix derivation from gameplay
  generateNixDerivation() {
    const prog = this.exportProgram();
    
    return `{
  description = "FRACTRAN program generated from gameplay";
  
  outputs = { self }:
    let
      # FRACTRAN program from player movements
      program = [
        ${prog.program.map(f => `{ n = ${f.n}; d = ${f.d}; }`).join('\n        ')}
      ];
      
      # Player state history
      moves = [
        ${prog.moves.slice(0, 10).map(m => 
          `{ frame = ${m.frame}; state = ${m.state}; }`
        ).join('\n        ')}
      ];
      
      # Execute FRACTRAN
      execute = state: prog:
        if prog == [] then state
        else
          let
            frac = builtins.head prog;
            result = state * frac.n;
          in
            if (result / frac.d) * frac.d == result
            then execute (result / frac.d) (builtins.tail prog)
            else execute state (builtins.tail prog);
      
      result = execute ${prog.initial_state} program;
      
    in {
      inherit program moves result;
      
      witness = {
        initial = ${prog.initial_state};
        final = ${prog.final_state};
        steps = ${prog.program.length};
        timestamp = "${prog.timestamp}";
      };
    };
}`;
  }
}

// Integrate with flying game
class FlyingGameWithWitness {
  constructor(canvas) {
    this.canvas = canvas;
    this.ctx = canvas.getContext('2d');
    this.recorder = new FRACTRANWitnessRecorder();
    
    this.ship = { x: 0, y: 0, z: 0, vx: 0, vy: 0, vz: 0 };
    this.sector = 0;
    this.frame = 0;
    this.recording = true;
  }
  
  update(dt) {
    this.frame++;
    
    // Update ship position
    this.ship.x += this.ship.vx * dt;
    this.ship.y += this.ship.vy * dt;
    this.ship.z += this.ship.vz * dt;
    
    // Record position every 10 frames
    if (this.recording && this.frame % 10 === 0) {
      this.recorder.recordPosition(this.ship.x, this.ship.y, this.ship.z);
      this.recorder.recordFrame(this.frame, {
        x: this.ship.vx,
        y: this.ship.vy,
        z: this.ship.vz
      });
    }
    
    // Check sector boundaries (71x59x47 space)
    const newSector = Math.floor(this.ship.x / 100) % 71;
    if (newSector !== this.sector) {
      this.recorder.recordSectorChange(this.sector, newSector);
      this.sector = newSector;
    }
  }
  
  handleInput(key) {
    const speed = 5;
    switch(key) {
      case 'w': this.ship.vz = -speed; break;
      case 's': this.ship.vz = speed; break;
      case 'a': this.ship.vx = -speed; break;
      case 'd': this.ship.vx = speed; break;
      case 'q': this.ship.vy = speed; break;
      case 'e': this.ship.vy = -speed; break;
      case ' ': this.ship.vx = this.ship.vy = this.ship.vz = 0; break;
    }
  }
  
  exportWitness() {
    return this.recorder.exportProgram();
  }
  
  exportNix() {
    return this.recorder.generateNixDerivation();
  }
  
  render() {
    this.ctx.fillStyle = '#000';
    this.ctx.fillRect(0, 0, this.canvas.width, this.canvas.height);
    
    // Draw ship
    this.ctx.fillStyle = '#ff0';
    this.ctx.font = '24px monospace';
    this.ctx.fillText('🚀', this.canvas.width/2, this.canvas.height/2);
    
    // Draw HUD
    this.ctx.fillStyle = '#0f0';
    this.ctx.font = '12px monospace';
    this.ctx.fillText(`Sector: ${this.sector}`, 10, 20);
    this.ctx.fillText(`Position: ${Math.floor(this.ship.x)}, ${Math.floor(this.ship.y)}, ${Math.floor(this.ship.z)}`, 10, 40);
    this.ctx.fillText(`Frame: ${this.frame}`, 10, 60);
    this.ctx.fillText(`FRACTRAN ops: ${this.recorder.program.length}`, 10, 80);
  }
}

window.FRACTRANWitnessRecorder = FRACTRANWitnessRecorder;
window.FlyingGameWithWitness = FlyingGameWithWitness;
