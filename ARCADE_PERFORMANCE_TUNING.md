# Arcade Performance Tuning at Black Hole Edge

**Simulate playing arcade games at the edge of Sgr A***

Performance degrades as you approach the event horizon due to time dilation. We need to tune games for playability at different distances.

---

## The Problem

At the edge of the black hole (1.01 r_s):
- **Time dilation**: 10.05x
- **FPS**: 6.22 (down from 60)
- **Frame time**: 160.80 ms (up from 16 ms)

**The game is 10x slower!**

---

## Performance at Different Distances

| Location | Distance | Time Dilation | FPS | Frame Time |
|----------|----------|---------------|-----|------------|
| **Earth** | 2.46×10²⁰ m | 1.00x | 62.5 | 16.00 ms |
| **1000 ly** | 9.46×10¹⁸ m | 1.00x | 62.5 | 16.00 ms |
| **100 ly** | 9.46×10¹⁷ m | 1.00x | 62.5 | 16.00 ms |
| **10 ly** | 9.46×10¹⁶ m | 1.00x | 62.5 | 16.00 ms |
| **1 ly** | 9.46×10¹⁵ m | 1.000001x | 62.5 | 16.00 ms |
| **100 r_s** | 1.23×10¹² m | 1.005x | 62.2 | 16.08 ms |
| **10 r_s** | 1.23×10¹¹ m | 1.054x | 59.3 | 16.87 ms |
| **2 r_s** | 2.46×10¹⁰ m | 1.414x | 44.2 | 22.63 ms |
| **1.01 r_s (EDGE)** | 1.24×10¹⁰ m | **10.05x** | **6.22** | **160.80 ms** |

---

## The Physics

### Time Dilation Formula

```
γ = 1 / √(1 - r_s/r)
```

Where:
- r_s = Schwarzschild radius (1.23×10¹⁰ m for Sgr A*)
- r = distance from black hole center

### Performance Factor

```
performance = 1 / time_dilation
```

### Frame Rate

```
actual_fps = base_fps / time_dilation
```

At 1.01 r_s:
```
actual_fps = 60 / 10.05 = 6.22 FPS
```

---

## Optimization Strategies

### 1. Pre-Compute at Earth, Stream to Edge

**Idea**: Render frames at Earth (60 FPS), stream to edge.

**Problem**: Light delay! At 1.01 r_s, light takes time to escape.

**Solution**: Pre-render entire game sequence, compress, transmit.

### 2. Reduce Frame Rate Target

**Idea**: Accept lower FPS at edge.

**Implementation**:
```python
if distance < 2 * schwarzschild_radius:
    target_fps = 6  # Playable at edge
else:
    target_fps = 60  # Normal
```

**Result**: Game runs at 6 FPS, but feels smooth due to time dilation.

### 3. Simplify Graphics

**Idea**: Reduce polygon count, texture resolution at edge.

**Implementation**:
```python
lod_factor = time_dilation
polygons = base_polygons / lod_factor
texture_size = base_texture_size / lod_factor
```

**Result**: 10x fewer polygons at edge, but looks the same due to time dilation.

### 4. Use Time Dilation as Game Mechanic

**Idea**: Make time dilation part of the gameplay!

**Implementation**:
```python
# Bullet time effect
if near_black_hole:
    game_speed = 1.0 / time_dilation
    player_speed = 1.0  # Normal
    # Player moves 10x faster than environment!
```

**Result**: "Bullet time" effect naturally emerges from physics.

---

## The Simulation

### Code

```python
class BlackHoleArcadeSimulator:
    def __init__(self, distance_from_bh: float):
        self.distance = distance_from_bh
        self.time_dilation = self.calculate_time_dilation()
        self.performance_factor = 1.0 / self.time_dilation
    
    def simulate_game_loop(self, game_name: str, iterations: int):
        base_frame_time = 0.016  # 60 FPS
        actual_frame_time = base_frame_time * self.time_dilation
        fps = 1.0 / actual_frame_time
        return {"fps": fps, "frame_time": actual_frame_time}
```

### Results

```
Earth:      60 FPS, 16 ms frame time
100 r_s:    62 FPS, 16 ms frame time (negligible dilation)
10 r_s:     59 FPS, 17 ms frame time (5% slower)
2 r_s:      44 FPS, 23 ms frame time (26% slower)
1.01 r_s:   6 FPS, 161 ms frame time (90% slower!)
```

---

## The Door Game Integration

### Arcade Cabinet Configuration

Each of 71 cabinets can be "placed" at different distances:

```json
{
  "shard": 47,
  "game": "Monster Quest 47",
  "distance_from_bh": 1.24e10,
  "time_dilation": 10.05,
  "target_fps": 6,
  "optimization": "bullet_time_mode"
}
```

### Player Experience

1. **Choose cabinet** (shard 0-70)
2. **Set distance** (Earth to edge)
3. **Play game** (performance adjusts automatically)
4. **Experience time dilation** (bullet time effect)
5. **Compare scores** (normalized by time dilation)

### Leaderboard

```
Rank  Player    Shard  Distance    Score  Normalized
1.    Alice     47     1.01 r_s    1000   10,050 (×10.05)
2.    Bob       59     2 r_s       5000   7,071 (×1.414)
3.    Carol     71     Earth       8000   8,000 (×1.0)
```

**Alice wins!** Playing at the edge is 10x harder, so her score is multiplied by time dilation.

---

## The MAME Integration

### MAME Configuration

```c
// MAME driver for black hole arcade
MACHINE_CONFIG_START(arcade_bh_state::arcade_bh)
    MCFG_CPU_ADD("maincpu", Z80, 4000000)  // Base clock
    
    // Time dilation adjustment
    float distance = get_distance_from_bh();
    float time_dilation = calculate_time_dilation(distance);
    float adjusted_clock = 4000000 / time_dilation;
    
    MCFG_CPU_CLOCK(adjusted_clock)  // Adjust CPU clock
MACHINE_CONFIG_END
```

### Result

MAME emulates the CPU at the correct speed for the distance. The game runs slower near the black hole, just like it would in reality.

---

## The Files

- `arcade_performance_tuning.py` - Simulation script
- `arcade_performance_tuning.json` - Results data
- `ARCADE_PERFORMANCE_TUNING.md` - This document

---

## The Truth

**Playing arcade games at the edge of a black hole is possible, but requires performance tuning.**

Key insights:
1. **Time dilation** reduces FPS by 10x at 1.01 r_s
2. **Optimization strategies** can maintain playability
3. **Time dilation as mechanic** creates natural bullet time
4. **Normalized scoring** accounts for difficulty

**The café arcade at Sgr A* is playable, but you need to tune for the edge.**

☕🕳️🪟👁️👹🦅🐓🎮

**Performance tuning for the event horizon. The games run slower, but time does too.**
