# Nix-Wars Matrix Rain: Escaped RDFa Emoji Lifting

**Lift game states into emoji matrix rain with RDFa encoding, integrated with LMFDB pilot**

## Integration with Zone 42 Orbit Pilot

The Nix-Wars states can be lifted into the existing LMFDB pilot interface at:
`~/projects/kiro/data/lmfdb-hf-dataset/pilot.html`

## Architecture

```
Nix-Wars State → RDFa → Emoji → Orbit → Pilot Interface
```

### Mapping

- **Game States** → **Curve Orbits**
- **Ships** → **Pilot Ship**
- **Sectors** → **Orbit Positions**
- **Commitments** → **Curve Labels**
- **zkPerf** → **Proof Generation**

## Usage

### 1. Lift States to Pilot Format
```bash
python3 lift-to-pilot.py states/*/result/state.json > nix-wars-orbits.json
```

### 2. Load in Pilot
```javascript
// In pilot.html
fetch('nix-wars-orbits.json')
  .then(r => r.json())
  .then(data => loadNixWarsOrbits(data));
```

### 3. Navigate Game States
- Fly to orbit = View game state
- Collect curve = Capture commitment
- Combine curves = Consensus resolution
- Warp drive = State transition

## The Lifting

Each Nix-Wars state becomes an orbit:

```javascript
{
  label: "State 4: Alpha→71",
  emoji: "🌓🌌🌔🌗🌖🌖🌓🌑",
  commitment: "2c36552088ccdd6d...",
  rdfa: "<escaped_rdfa>",
  position: { angle: 4.2, radius: 350 },
  vibe: 7,
  zkperf: { cycles: 1903710 }
}
```

## Pilot Controls

- **WASD**: Navigate space
- **Space**: Land on orbit (view state)
- **E**: Collect curve (capture commitment)
- **Click orbit**: Select for warp
- **W**: Warp drive (state transition)

## Deploy

```bash
cp nix-wars-matrix.html ~/projects/kiro/data/lmfdb-hf-dataset/nix-wars.html
cd ~/projects/kiro/data/lmfdb-hf-dataset/
# Edit pilot.html to load nix-wars-orbits.json
```

View at: file:///home/mdupont/projects/kiro/data/lmfdb-hf-dataset/pilot.html

**The game becomes navigable space. The states become orbits.** 🚀🌌
