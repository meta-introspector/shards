# SCP-ZK71 - Toxic Code Containment

Safe handling of hazardous code repositories with zero-knowledge verification and 71-shard isolation.

## Build

```bash
cd scp-zk71
cargo build --release
```

## Usage

### Full Containment Workflow

```bash
cargo run --release -- contain --url https://github.com/suspicious/repo
```

Output:
```
╔════════════════════════════════════════════════════════════╗
║           SCP-ZK71 CONTAINMENT PROTOCOL                    ║
╚════════════════════════════════════════════════════════════╝

Step 1: Cloning to quarantine...
⚠️  INITIATING SCP-ZK71 CONTAINMENT
Repository: https://github.com/suspicious/repo
✓ Cloned to quarantine
  Hash: 8f3e2d1c4b5a6789...
  ZK Proof: a1b2c3d4...

Step 2: Scanning for toxicity...
=== TOXICITY SCAN ===
Toxicity Level: Hazardous
Findings: 3
  [Hazardous] main.py:42 - Dynamic code execution
  [Caution] api.py:15 - Unverified network request
  [Toxic] config.py:8 - Potential hardcoded credential

Step 3: Isolating to 71 shards...
=== 71-SHARD ISOLATION ===
Isolated 150 files across 71 shards

Step 4: Rewriting safely...
=== SAFE REWRITE ===
✓ Rewrote 150 files

✓ CONTAINMENT COMPLETE
  Quarantine: /tmp/scp-zk71-quarantine
  Clean output: /tmp/scp-zk71-clean
```

### Individual Commands

```bash
# Clone with ZK verification
cargo run --release -- clone \
  --url https://github.com/repo \
  --quarantine /tmp/quarantine

# Scan for toxicity
cargo run --release -- scan --path /tmp/quarantine

# Isolate to 71 shards
cargo run --release -- isolate --path /tmp/quarantine

# Safe rewrite
cargo run --release -- rewrite \
  --path /tmp/quarantine \
  --output /tmp/clean
```

## Toxicity Levels

- **Safe**: Well-maintained, audited code
- **Caution**: Outdated dependencies, minor issues
- **Hazardous**: Known CVEs, `eval()`, `exec()`
- **Toxic**: Hardcoded credentials, malicious patterns
- **Keter**: Self-modifying code, cannot safely rewrite

## What It Does

### 1. ZK Clone
- Clones repository to isolated quarantine
- Computes cryptographic hash of entire repo
- Generates zero-knowledge proof of safe cloning

### 2. Toxicity Scan
- Detects dangerous patterns:
  - `eval()`, `exec()` - Dynamic code execution
  - `password =` - Hardcoded credentials
  - `__import__`, `compile()` - Self-modifying code
- Assigns toxicity level

### 3. 71-Shard Isolation
- Distributes files across 71 isolated shards
- Each shard processed independently
- Prevents cross-contamination

### 4. Safe Rewrite
- Removes toxic patterns
- Sanitizes dangerous code
- Outputs clean version
- Refuses to rewrite KETER-level code

## Safety Features

- **No network access** during processing
- **Read-only** quarantine environment
- **Isolated shards** prevent contamination
- **ZK verification** proves safe handling
- **Automatic sanitization** of toxic patterns

## Emergency Response

If KETER-level detected:
```bash
# Manual cleanup required
rm -rf /tmp/scp-zk71-quarantine
# Review findings before proceeding
```

## Integration with CICADA-71

- Uses 71-shard architecture
- ZK proofs for verification
- Harmonic distribution of files
- Safe handling of external code

## Example

```bash
# Clone and contain a repository
cargo run --release -- contain \
  --url https://github.com/meta-introspector/introspector

# Output shows toxicity level and safe rewrite
```
