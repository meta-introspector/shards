// ZX81 BBS Terminal Emulator for Nix-Wars
// Renders game in 32x24 character display

class ZX81Terminal {
  constructor(canvas) {
    this.canvas = canvas;
    this.ctx = canvas.getContext('2d');
    this.cols = 32;
    this.rows = 24;
    this.charWidth = 8;
    this.charHeight = 8;
    this.buffer = Array(this.rows).fill(null).map(() => Array(this.cols).fill(' '));
    
    canvas.width = this.cols * this.charWidth;
    canvas.height = this.rows * this.charHeight;
  }
  
  clear() {
    this.buffer = Array(this.rows).fill(null).map(() => Array(this.cols).fill(' '));
  }
  
  print(x, y, text, inverse = false) {
    for (let i = 0; i < text.length && x + i < this.cols; i++) {
      this.buffer[y][x + i] = inverse ? '\u2588' + text[i] : text[i];
    }
  }
  
  render() {
    this.ctx.fillStyle = '#000';
    this.ctx.fillRect(0, 0, this.canvas.width, this.canvas.height);
    
    this.ctx.fillStyle = '#fff';
    this.ctx.font = '8px monospace';
    
    for (let y = 0; y < this.rows; y++) {
      for (let x = 0; x < this.cols; x++) {
        const char = this.buffer[y][x];
        if (char.startsWith('\u2588')) {
          // Inverse video
          this.ctx.fillStyle = '#fff';
          this.ctx.fillRect(x * this.charWidth, y * this.charHeight, this.charWidth, this.charHeight);
          this.ctx.fillStyle = '#000';
          this.ctx.fillText(char[1], x * this.charWidth, (y + 1) * this.charHeight - 2);
          this.ctx.fillStyle = '#fff';
        } else {
          this.ctx.fillText(char, x * this.charWidth, (y + 1) * this.charHeight - 2);
        }
      }
    }
  }
}

class NixWarsBBS {
  constructor(terminal, engine) {
    this.term = terminal;
    this.engine = engine;
    this.mode = 'menu';
    this.cursor = 0;
  }
  
  drawBorder() {
    const top = '+' + '-'.repeat(30) + '+';
    this.term.print(0, 0, top);
    this.term.print(0, 23, top);
    for (let y = 1; y < 23; y++) {
      this.term.print(0, y, '|');
      this.term.print(31, y, '|');
    }
  }
  
  drawMenu() {
    this.term.clear();
    this.drawBorder();
    
    this.term.print(8, 2, 'NIX-WARS BBS', true);
    this.term.print(6, 4, 'TRADEWARS 71 EDITION');
    this.term.print(2, 7, '1. VIEW SECTORS');
    this.term.print(2, 8, '2. WARP DRIVE');
    this.term.print(2, 9, '3. INVENTORY');
    this.term.print(2, 10, '4. ZKPERF PROOF');
    this.term.print(2, 11, '5. SOLANA SYNC');
    this.term.print(2, 12, 'Q. QUIT');
    
    this.term.print(2, 15, 'SHIP: ALPHA');
    this.term.print(2, 16, 'SECTOR: ' + this.engine.ship.sector);
    this.term.print(2, 17, 'CREDITS: ' + this.engine.ship.credits);
    
    this.term.print(2, 20, 'SELECT>');
  }
  
  drawSectors() {
    this.term.clear();
    this.drawBorder();
    
    this.term.print(10, 2, 'SECTOR MAP', true);
    
    const states = this.engine.states.slice(0, 15);
    for (let i = 0; i < states.length; i++) {
      const state = states[i];
      const marker = i === this.cursor ? '>' : ' ';
      const round = ('R' + state.round).padEnd(4);
      const sector = ('S' + (state.ships?.alpha?.sector || 0)).padEnd(5);
      this.term.print(2, 4 + i, marker + round + sector);
    }
    
    this.term.print(2, 21, 'ARROWS:MOVE ENTER:SELECT');
  }
  
  drawWarp() {
    this.term.clear();
    this.drawBorder();
    
    this.term.print(10, 2, 'WARP DRIVE', true);
    this.term.print(2, 5, 'FROM SECTOR: ' + this.engine.ship.sector);
    this.term.print(2, 7, 'TO SECTOR: __');
    this.term.print(2, 10, 'ENTER DESTINATION (0-71)');
    this.term.print(2, 12, 'PRESS W TO ENGAGE');
  }
  
  render() {
    switch(this.mode) {
      case 'menu': this.drawMenu(); break;
      case 'sectors': this.drawSectors(); break;
      case 'warp': this.drawWarp(); break;
    }
    this.term.render();
  }
  
  handleKey(key) {
    if (this.mode === 'menu') {
      if (key === '1') this.mode = 'sectors';
      else if (key === '2') this.mode = 'warp';
      else if (key === 'q') this.mode = 'quit';
    } else if (this.mode === 'sectors') {
      if (key === 'ArrowUp') this.cursor = Math.max(0, this.cursor - 1);
      else if (key === 'ArrowDown') this.cursor = Math.min(this.engine.states.length - 1, this.cursor + 1);
      else if (key === 'Escape') this.mode = 'menu';
    } else if (this.mode === 'warp') {
      if (key === 'Escape') this.mode = 'menu';
    }
    this.render();
  }
}

window.ZX81Terminal = ZX81Terminal;
window.NixWarsBBS = NixWarsBBS;
