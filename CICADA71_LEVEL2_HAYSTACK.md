# CICADA-71 Level 2: Haystack Search

Find the j-invariant needle in the knowledge base haystack.

## Challenge

**Given**: 10 knowledge base tapes (100GB compressed data)

**Find**: j-invariant coefficients hidden in the data

**Needles**:
- `744` - j-invariant constant term
- `196883` - Monster group smallest dimension
- `196884` - j-invariant coefficient (196883 + 1)
- `21493760` - j-invariant q^2 coefficient
- `j-invariant` - Literal string

## Where to Look

### OEIS (Tape 1)
- **A000521**: Coefficients of j-invariant
- **A001379**: Order of Monster group
- **A007379**: Monstrous moonshine sequences
- **A097340**: McKay-Thompson series

### Wikidata (Tape 2)
- **Q193724**: Monster group entity
- **Q1139519**: Monstrous moonshine
- **Q334638**: Griess algebra
- Properties linking to j-invariant

### LMFDB (Tape 4)
- Modular forms database
- j-invariant entries
- Moonshine connections
- Automorphic forms

### Gutenberg (Tape 6)
- Mathematical texts mentioning Monster
- Number theory books
- Historical papers

## Algorithm

```rust
for tape in tapes {
    for line in tape.lines() {
        for needle in needles {
            if line.contains(needle) {
                record_match(tape, line, needle);
            }
        }
    }
}

// Encode matches as Gödel number
godel = encode_matches(matches);
```

## Gödel Encoding

Each match contributes to the final Gödel number:

```
G = 2^(match_1) × 3^(match_2) × 5^(match_3) × ... × 353^(match_71)
```

Where `match_i` is the coefficient found at position i.

## Expected Output

```
📼 tape-oeis.dat (15 matches)
   Line 521: 196884 → "A000521: j-invariant coefficients..."
   Line 1379: 196883 → "A001379: Monster group order..."
   
📼 tape-lmfdb.dat (8 matches)
   Line 42: j-invariant → "Modular form j(τ) = q^(-1) + 744..."
   
📼 tape-wikidata.dat (3 matches)
   Line 193724: 196883 → "Q193724: Monster group dimension..."

✅ Found 26 matches!

Gödel encoding: 2^744 × 3^196884 × 5^21493760 × ...
```

## Verification

1. Count matches per tape
2. Verify Monster dimension appears (196,883)
3. Confirm j-invariant constant (744)
4. Check Moonshine relation (196,884 = 196,883 + 1)
5. Encode as Gödel number

## Build & Run

```bash
# Compile
rustc haystack.rs -o haystack

# Generate tapes first
cd ../tapes
cargo run

# Search
cd ../level2
./haystack

# Expected: 26 matches across OEIS, LMFDB, Wikidata
```

## Difficulty

- **Level 0**: Calculate simple Gödel number (trivial)
- **Level 1**: Encode j-invariant coefficients (easy)
- **Level 2**: Find j-invariant in 100GB haystack (medium)
- **Level 3**: Decode Moonshine from Monster (hard)

## Why This Matters

Real-world cryptanalysis often involves:
- Searching massive datasets
- Pattern recognition
- Cross-referencing multiple sources
- Verifying mathematical relationships

This simulates finding cryptographic keys hidden in public data.
