# LMFDB Flying Game → FRACTRAN Program

**Playing the game generates a FRACTRAN program that encodes your movements**

## The Concept

Every player action becomes a FRACTRAN fraction:
- **Position** → `2^x × 3^y × 5^z`
- **Velocity** → Prime exponents
- **Sector change** → `prime_to / prime_from`

## How It Works

### 1. Position Encoding
```javascript
// Player at (10, 20, 30)
state = 2^1 × 3^2 × 5^3 = 2 × 9 × 125 = 2250
```

### 2. Movement as FRACTRAN
```javascript
// Move from state A to state B
fraction = { n: stateB, d: stateA }
program.push(fraction)
```

### 3. Sector Transitions
```javascript
// Warp from sector 42 to sector 71
fraction = { n: 71, d: 47 }  // Using Monster primes
```

## Example Gameplay → FRACTRAN

### Player Actions
1. Start at (0, 0, 0) → state = 1
2. Move to (10, 0, 0) → state = 2
3. Move to (10, 10, 0) → state = 6
4. Move to (10, 10, 10) → state = 30

### Generated FRACTRAN Program
```nix
program = [
  { n = 2; d = 1; }    # Move X
  { n = 6; d = 2; }    # Move Y
  { n = 30; d = 6; }   # Move Z
];
```

### Execution
```
1 → 2 → 6 → 30
```

## Witness Structure

```json
{
  "program": [
    {"n": 2, "d": 1},
    {"n": 6, "d": 2},
    {"n": 30, "d": 6}
  ],
  "moves": [
    {"frame": 10, "state": 2},
    {"frame": 20, "state": 6},
    {"frame": 30, "state": 30}
  ],
  "initial_state": 1,
  "final_state": 30,
  "timestamp": "2026-02-15T06:42:19Z"
}
```

## Generated Nix Derivation

```nix
{
  description = "FRACTRAN program generated from gameplay";
  
  outputs = { self }:
    let
      program = [
        { n = 2; d = 1; }
        { n = 6; d = 2; }
        { n = 30; d = 6; }
      ];
      
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
      
      result = execute 1 program;
      
    in {
      inherit program result;
      
      witness = {
        initial = 1;
        final = 30;
        steps = 3;
      };
    };
}
```

## Usage

### 1. Play the Game
```bash
firefox flying-fractran.html
# Use WASD/QE to fly around
```

### 2. Export Witness
Click "Export JSON" or "Download"

### 3. Convert to Nix
```bash
# Witness is automatically converted to Nix derivation
# Click "Export Nix" to see the code
```

### 4. Build with Nix
```bash
# Save exported Nix to flake.nix
nix build
# Result contains FRACTRAN execution trace
```

## Properties

### ✅ Gameplay = Computation
Every move is a FRACTRAN operation

### ✅ Reproducible
Same movements = same FRACTRAN program

### ✅ Verifiable
Anyone can execute the FRACTRAN program

### ✅ Composable
Combine multiple gameplay sessions

### ✅ Pure Functional
Nix derivation from gameplay

## The Win

**Playing the game produces a FRACTRAN program.**

This means:
1. Gameplay is computation
2. Movements are provable
3. Sessions are reproducible
4. History is executable
5. Fun generates math

**You're not just playing a game. You're writing a FRACTRAN program.** 🎮➡️🔢
