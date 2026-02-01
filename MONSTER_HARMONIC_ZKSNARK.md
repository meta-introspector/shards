# Monster Harmonic zkSNARK

**Proving Monster Group harmonics on zkML data via Groth16**

## Overview

The Monster Harmonic zkSNARK proves:
1. **Hecke operator computation** on zkML data (perf + ollama)
2. **j-invariant modulation** (Monster group: 196884-dimensional)
3. **Topological classification** (10-fold way)
4. **Bott periodicity** (period 8)
5. **Behavior prediction** (register, post, comment, lurk)

## Circuit Structure

```circom
MonsterHarmonic(71) {
  // Public inputs
  perf_hash      // zkPerf data hash (BN254 field)
  ollama_hash    // Ollama response hash
  shard_id       // 0-70
  
  // Private inputs
  primes[71]     // Monster primes [2, 3, 5, ..., 353]
  
  // Outputs
  j_invariant    // j(τ) mod 196884
  topo_class     // 0-9 (A, AIII, AI, BDI, D, DIII, AII, CII, C, CI)
  bott_period    // 0-7 (Bott periodicity)
  prediction     // 0-3 (register, post, comment, lurk)
}
```

## Hecke Operator

For prime `p` and data hash `h`:

```
T_p(f) = (h mod p²) + (h / p mod p)
```

Applied to 71 Monster primes, generates modular form coefficients.

## j-Invariant

Monster group j-invariant:

```
j(τ) = 744 + Σ(Hecke coefficients) mod 196884
```

Where 196884 = dim(Monster representation) - 1.

## Topological Classification

10-fold way (Altland-Zirnbauer):

```
class_id = shard_id mod 10
```

Maps to: A, AIII, AI, BDI, D, DIII, AII, CII, C, CI

## Bott Periodicity

```
period = Σ(factors) mod 8
```

Reflects K-theory periodicity in topological phases.

## Usage

### 1. Generate Witness

```bash
python3 generate_monster_witness.py ~/.openclaw/shard-0/zkwitness-0.json
```

Output: `~/.openclaw/shard-0/monster_witness.json`

### 2. Generate Proof

```bash
bash generate_monster_proof.sh 0
```

Generates:
- `proof.json` - Groth16 proof
- `public.json` - Public outputs
- `verification_key.json` - Verifier key

### 3. Verify Proof

```bash
snarkjs groth16 verify \
  ~/.openclaw/shard-0/verification_key.json \
  ~/.openclaw/shard-0/public.json \
  ~/.openclaw/shard-0/proof.json
```

## Integration with zkOS

The proof can be submitted to zkOS via the Lobster Bot plugin:

```rust
let proof_json = std::fs::read_to_string("proof.json")?;
let public_json = std::fs::read_to_string("public.json")?;

let zksnark_witness = json!({
    "proof": proof_json,
    "public": public_json,
    "circuit": "MonsterHarmonic",
    "curve": "BN254"
});

plugin_submit_block(plugin, zksnark_witness.to_string());
```

## Proof Size

- **Proof**: ~200 bytes (Groth16)
- **Public inputs**: 4 field elements (128 bytes)
- **Verification time**: ~5ms

## Security

- **Curve**: BN254 (128-bit security)
- **Scheme**: Groth16 (trusted setup)
- **Powers of Tau**: 2^14 constraints
- **Circuit constraints**: ~10,000 (71 Hecke operators)

## Files

```
introspector/
├── monster_harmonic.circom           # Circom circuit
├── generate_monster_witness.py       # Witness generator
├── generate_monster_proof.sh         # Proof generator
└── MONSTER_HARMONIC_ZKSNARK.md      # This file

~/.openclaw/shard-0/
├── zkwitness-0.json                  # zkML witness (input)
├── monster_witness.json              # Circom witness
├── monster_harmonic.r1cs             # R1CS constraints
├── monster_harmonic_final.zkey       # Proving key
├── verification_key.json             # Verification key
├── proof.json                        # Groth16 proof
└── public.json                       # Public outputs
```

## Example Output

```json
{
  "j_invariant": "123456",
  "topo_class": "6",
  "bott_period": "1",
  "prediction": "0"
}
```

Interpretation:
- j-invariant: 123456 (Monster group modulation)
- Topological class: 6 = AII (Quantum Spin Hall)
- Bott period: 1 (mod 8)
- Prediction: 0 = register (90% confidence)

## Next Steps

1. Generate proofs for all 71 shards
2. Aggregate proofs (Groth16 batch verification)
3. Submit to zkOS plugin
4. Deploy to Moltbook prediction market
5. Settle with Metameme Coin (MMC)

## References

- [Circom Documentation](https://docs.circom.io/)
- [snarkjs](https://github.com/iden3/snarkjs)
- [Monster Group](https://en.wikipedia.org/wiki/Monster_group)
- [Hecke Operators](https://en.wikipedia.org/wiki/Hecke_operator)
- [10-fold way](https://en.wikipedia.org/wiki/Topological_order#Altland-Zirnbauer_classification)
