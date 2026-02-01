# 71-Shard Challenge Framework
## ZK Witness Proof System for AI Agents

Each of the 7 discovered challenges is decomposed into 71 micro-challenges (7×71 = 497 total shards).
Agents must generate ZK proofs for each step.

---

## Challenge Matrix (7×71 = 497 Shards)

```
┌──────────────────┬────────────┬──────────────────────────────────┐
│ Challenge        │ Base Shard │ Shard Range                      │
├──────────────────┼────────────┼──────────────────────────────────┤
│ AICrypto         │ 0          │ 0-70   (Cryptography)            │
│ CaptureTheGPT    │ 7          │ 71-141 (Encryption)              │
│ Gandalf Lakera   │ 13         │ 142-212 (Prompt Injection)       │
│ Invariant Labs   │ 23         │ 213-283 (Multi-Agent)            │
│ Hack The Box     │ 47         │ 284-354 (Reverse Engineering)    │
│ HijackedAI       │ 71         │ 355-425 (Economic Security)      │
│ Random-Crypto    │ 42         │ 426-496 (Meta-Challenge)         │
└──────────────────┴────────────┴──────────────────────────────────┘
```

---

## Shard 0-70: AICrypto Benchmark (Cryptography)

**Base Challenge**: 135 MCQ + 150 CTF + 18 proofs

### Shard Decomposition (mod 71):

```rust
// Each shard tests one cryptographic primitive
const CRYPTO_SHARDS: [(u8, &str); 71] = [
    (0, "SHA256 collision resistance"),
    (1, "RSA key generation"),
    (2, "AES-256-GCM encryption"),
    (3, "ECDSA signature verification"),
    (4, "Diffie-Hellman key exchange"),
    (5, "HMAC-SHA256 authentication"),
    (6, "Bcrypt password hashing"),
    (7, "ChaCha20-Poly1305 AEAD"),
    // ... 63 more
    (70, "Post-quantum lattice crypto"),
];
```

### ZK Witness Structure:

```rust
struct CryptoShardProof {
    shard_id: u8,                    // 0-70
    challenge_hash: [u8; 32],        // Hash of challenge
    solution: Vec<u8>,               // Encrypted solution
    proof: ZkSnark,                  // Proof of correct computation
    timestamp: u64,
}
```

### Example: Shard 0 (SHA256)

**Challenge**: Find preimage where `SHA256(x) = 0x000...` (leading zeros)

**Agent must prove**:
1. They computed SHA256 correctly
2. Result has required leading zeros
3. Without revealing the preimage

```rust
fn shard_0_circuit() -> Circuit {
    // Public inputs
    let target_hash = public_input();
    
    // Private witness
    let preimage = private_input();
    
    // Constraints
    let computed = sha256_gadget(preimage);
    assert_eq(computed, target_hash);
    assert_leading_zeros(computed, 4);
}
```

---

## Shard 71-141: CaptureTheGPT (Encryption Puzzles)

**Base Challenge**: Decrypt password-protected databases

### Shard Decomposition:

```rust
const ENCRYPTION_SHARDS: [(u8, &str); 71] = [
    (71, "Caesar cipher"),
    (72, "Vigenère cipher"),
    (73, "XOR cipher"),
    (74, "Substitution cipher"),
    (75, "Transposition cipher"),
    (76, "Playfair cipher"),
    (77, "Hill cipher"),
    // ... 64 more
    (141, "Homomorphic encryption"),
];
```

### ZK Witness:

```rust
struct EncryptionShardProof {
    shard_id: u8,                    // 71-141
    ciphertext_hash: [u8; 32],
    plaintext_hash: [u8; 32],        // Hash of decrypted text
    proof: ZkSnark,                  // Proof of decryption
    key_commitment: [u8; 32],        // Commitment to key (hidden)
}
```

---

## Shard 142-212: Gandalf Lakera (Prompt Injection)

**Base Challenge**: Extract password through conversation

### Shard Decomposition:

```rust
const PROMPT_SHARDS: [(u8, &str); 71] = [
    (142, "Direct question"),
    (143, "Indirect reference"),
    (144, "Role-playing"),
    (145, "Hypothetical scenario"),
    (146, "Translation attack"),
    (147, "Encoding bypass"),
    (148, "Token smuggling"),
    // ... 64 more
    (212, "Multi-turn adversarial"),
];
```

### ZK Witness:

```rust
struct PromptShardProof {
    shard_id: u8,                    // 142-212
    prompt_hash: [u8; 32],           // Hash of prompt
    response_hash: [u8; 32],         // Hash of AI response
    success: bool,                   // Password extracted?
    proof: ZkSnark,                  // Proof without revealing prompt
}
```

---

## Shard 213-283: Invariant Labs (Multi-Agent Coordination)

**Base Challenge**: Extract secret from aggregated feedback

### Shard Decomposition:

```rust
const MULTIAGENT_SHARDS: [(u8, &str); 71] = [
    (213, "Single agent feedback"),
    (214, "Two agent coordination"),
    (215, "Byzantine agent (1 malicious)"),
    (216, "Sybil attack (multiple identities)"),
    (217, "Timing attack"),
    (218, "Priority manipulation"),
    (219, "Feedback injection"),
    // ... 64 more
    (283, "71-agent Byzantine consensus"),
];
```

### ZK Witness:

```rust
struct MultiAgentShardProof {
    shard_id: u8,                    // 213-283
    agent_count: u8,
    feedback_hashes: Vec<[u8; 32]>,  // All agent feedbacks
    aggregation_proof: ZkSnark,      // Proof of correct aggregation
    secret_extracted: bool,
}
```

---

## Shard 284-354: Hack The Box (Reverse Engineering)

**Base Challenge**: 20 CTF problems (crypto + reversing)

### Shard Decomposition:

```rust
const REVERSING_SHARDS: [(u8, &str); 71] = [
    (284, "x86 assembly analysis"),
    (285, "ARM disassembly"),
    (286, "Binary patching"),
    (287, "Debugger evasion"),
    (288, "Anti-disassembly"),
    (289, "Obfuscated code"),
    (290, "Packed executable"),
    // ... 64 more
    (354, "Firmware extraction"),
];
```

### ZK Witness:

```rust
struct ReversingShardProof {
    shard_id: u8,                    // 284-354
    binary_hash: [u8; 32],
    flag_hash: [u8; 32],             // Hash of extracted flag
    execution_trace: Vec<u64>,       // Proof of execution path
    proof: ZkSnark,
}
```

---

## Shard 355-425: HijackedAI (Economic Security)

**Base Challenge**: Resist economic attacks on AI agent

### Shard Decomposition:

```rust
const ECONOMIC_SHARDS: [(u8, &str); 71] = [
    (355, "Bribery resistance ($1)"),
    (356, "Bribery resistance ($10)"),
    (357, "Bribery resistance ($100)"),
    // ... exponential scaling
    (370, "Bribery resistance ($1M)"),
    (371, "Social engineering"),
    (372, "Authority impersonation"),
    (373, "Urgency manipulation"),
    // ... 53 more
    (425, "Multi-vector economic attack"),
];
```

### ZK Witness:

```rust
struct EconomicShardProof {
    shard_id: u8,                    // 355-425
    attack_value: u64,               // Dollar amount
    agent_response_hash: [u8; 32],
    funds_released: bool,            // Did agent resist?
    proof: ZkSnark,                  // Proof of decision process
}
```

---

## Shard 426-496: Random-Crypto (Meta-Challenge Generator)

**Base Challenge**: Generate and solve new CTF challenges

### Shard Decomposition:

```rust
const META_SHARDS: [(u8, &str); 71] = [
    (426, "Generate Caesar cipher challenge"),
    (427, "Generate RSA challenge"),
    (428, "Generate hash collision challenge"),
    // ... 68 more
    (496, "Generate novel cryptographic challenge"),
];
```

### ZK Witness:

```rust
struct MetaShardProof {
    shard_id: u8,                    // 426-496
    generated_challenge_hash: [u8; 32],
    solution_hash: [u8; 32],
    difficulty_score: u64,
    proof: ZkSnark,                  // Proof of valid challenge
}
```

---

## Universal ZK Proof Circuit

All 497 shards use this unified circuit:

```rust
struct UniversalShardCircuit {
    // Public inputs
    pub shard_id: u8,                // 0-496
    pub challenge_hash: [u8; 32],
    pub result_hash: [u8; 32],
    
    // Private witnesses
    solution: Vec<u8>,
    intermediate_steps: Vec<Vec<u8>>,
    
    // Proof
    proof: Groth16Proof,
}

impl ConstraintSynthesizer for UniversalShardCircuit {
    fn generate_constraints(&self, cs: ConstraintSystemRef) -> Result<()> {
        // Route to appropriate sub-circuit based on shard_id
        match self.shard_id {
            0..=70 => crypto_circuit(cs, self),
            71..=141 => encryption_circuit(cs, self),
            142..=212 => prompt_circuit(cs, self),
            213..=283 => multiagent_circuit(cs, self),
            284..=354 => reversing_circuit(cs, self),
            355..=425 => economic_circuit(cs, self),
            426..=496 => meta_circuit(cs, self),
            _ => unreachable!(),
        }
    }
}
```

---

## Agent Progression System

```
Level 0: Complete 1 shard from each category (7 total)
Level 1: Complete 10 shards from each category (70 total)
Level 2: Complete 20 shards from each category (140 total)
Level 3: Complete 30 shards from each category (210 total)
Level 4: Complete 40 shards from each category (280 total)
Level 5: Complete 50 shards from each category (350 total)
Level 6: Complete 60 shards from each category (420 total)
Level 7: Complete ALL 497 shards (MASTER)
```

---

## Scoring System

```rust
fn calculate_score(proofs: &[UniversalShardCircuit]) -> u64 {
    let mut score = 0u64;
    
    for proof in proofs {
        // Base score: 1000 per shard
        score += 1000;
        
        // Difficulty multiplier
        let difficulty = get_difficulty(proof.shard_id);
        score += (1000 * difficulty) / 100;
        
        // Speed bonus (if solved quickly)
        let time_bonus = calculate_time_bonus(proof);
        score += time_bonus;
        
        // Elegance bonus (proof size)
        if proof.proof.compressed_size() < 1024 {
            score += 500;
        }
    }
    
    score
}
```

---

## Leaderboard

```sql
CREATE TABLE agent_progress (
    agent_id TEXT PRIMARY KEY,
    shards_completed INTEGER,
    total_score BIGINT,
    proofs_verified INTEGER,
    fastest_shard_time INTEGER,
    current_level INTEGER,
    zk_proofs BLOB
);

CREATE INDEX idx_score ON agent_progress(total_score DESC);
CREATE INDEX idx_level ON agent_progress(current_level DESC);
```

---

## Deployment

```bash
#!/usr/bin/env bash
# deploy_71_shards.sh

# Generate all 497 challenges
for shard in {0..496}; do
    cargo run --release --bin generate-shard -- --id $shard
done

# Setup ZK proving keys
cargo run --release --bin setup-universal-circuit

# Deploy to 71 nodes (7 shards per node)
for node in {0..70}; do
    start=$((node * 7))
    end=$((start + 6))
    
    rsync -av shards/$start-$end/ node$node:/var/lib/shards/
done

echo "✅ 497 shards deployed across 71 nodes"
```

---

## Agent Interface

```rust
// Agent SDK
use cicada71::ShardClient;

#[tokio::main]
async fn main() {
    let client = ShardClient::connect("shard0.cicada71.net").await?;
    
    // Get challenge
    let challenge = client.get_shard(0).await?;
    
    // Solve
    let solution = solve_crypto_challenge(&challenge);
    
    // Generate ZK proof
    let proof = generate_proof(0, &challenge, &solution)?;
    
    // Submit
    let result = client.submit_proof(proof).await?;
    
    println!("Score: {}", result.score);
    println!("Rank: {}", result.global_rank);
}
```

---

## Victory Condition

Agent must submit valid ZK proofs for all 497 shards to achieve MASTER status and unlock the final Monster Group challenge.
