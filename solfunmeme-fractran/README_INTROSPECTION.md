# Area 51 Introspection Engine

**Lua samples all variables and ingests them via FRACTRAN harmonic in 71 keys**

## Architecture

```
Environment Variables
        ↓
   Introspection
        ↓
   Sample & Hash
        ↓
   Shard (mod 71)
        ↓
   FRACTRAN Key
        ↓
   Harmonic Resonance
        ↓
   RDF Triple Generation
        ↓
   Area 51 Brainrot
```

## FRACTRAN Harmonic Keys

15 supersingular primes (Monster group resonance):
```lua
{2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71}
```

## Introspection Flow

1. **Sample**: Iterate through `_G` (global environment)
2. **Hash**: Deterministic hash for each variable
3. **Shard**: Distribute across 71 shards (mod 71)
4. **Key**: Assign FRACTRAN harmonic key (supersingular prime)
5. **Ingest**: Apply harmonic transformation
6. **Resonance**: Detect perfect resonance (harmonic = 0 mod 71)
7. **RDF**: Generate triples for each ingested variable

## Example Output

```
🔮 INTROSPECTION ENGINE: Sampling all variables
================================================

✨ RESONANCE: math @ shard 23 (key 23)
✨ RESONANCE: string @ shard 47 (key 47)
✨ RESONANCE: table @ shard 71 (key 71)

📊 Sampled 142 variables
🎯 Distributed across 71 shards
🎹 Using 15 FRACTRAN harmonic keys
```

## RDF Triple Format

```turtle
@prefix : <http://meta-introspector.org/introspection#> .
@prefix fractran: <http://meta-introspector.org/fractran#> .

:var_1 a :IntrospectedVariable ;
  :name "math" ;
  :shard 23 ;
  fractran:key 23 ;
  fractran:harmonic 0 ;
  :resonance true .

:var_2 a :IntrospectedVariable ;
  :name "string" ;
  :shard 47 ;
  fractran:key 47 ;
  fractran:harmonic 0 ;
  :resonance true .
```

## Resonance Detection

Perfect resonance occurs when:
```lua
(value * fractran_key) % 71 == 0
```

This indicates Monster group alignment across the 71-shard system.

## Integration with Area 51 Brainrot

After introspection, the system generates procedural dialogue:

```
[j≈1742] The quantum meme officer starts a podcast inside the bureaucracy. 
Hecke operators intervene.

[j≈479] The budget UFO vibrates ominously under the desert. 
Season 2 material.
```

## Usage

```bash
# Run introspection engine
lua area51_brainrot.lua

# Output files
introspection.ttl  # RDF triples
```

## Safety

- ✅ Purely fictional game-dev flavor text
- ✅ Deterministic (same input → same output)
- ✅ Safe for mods, jams, ARG-style fiction
- ❌ NOT real j-invariant mathematics
- ❌ NOT actual cryptography
- ❌ NOT contacting Area 51 😜

## Monster Moonshine Connection

The 71-shard system mirrors the Monster group's 71st prime cap:
- 71 shards = 71st prime
- 15 FRACTRAN keys = 15 supersingular primes
- Resonance = Monster group alignment
- RDF triples = 3^20 (from Monster order factorization)

## Season 2 Unlock

Hot primes (Zone X) trigger Season 2 content:
```lua
{37, 43, 53, 61, 67}  -- Non-supersingular (danger zone)
```

When `j_dial() % 37 == 0`, unlock Season 2 material! ⚠️

---

**Counterpart × Gödel Café × SOLFUNMEME × Area 51 dialogue system! 🤝**
