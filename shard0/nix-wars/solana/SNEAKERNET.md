# Solana Sneakernet: Air-Gapped Transaction Transport

**Create transactions offline, transport via UUCP, submit when online**

## Architecture

```
Air-Gapped Machine          Sneakernet           Online Machine
┌─────────────────┐        ┌────────┐        ┌──────────────┐
│ Nix-Wars Game   │        │ UUCP   │        │ Solana RPC   │
│ Build state     │───────>│ Spool  │───────>│ Submit txn   │
│ Generate txn    │  USB   │ Files  │  USB   │ Get receipt  │
└─────────────────┘        └────────┘        └──────────────┘
```

## Workflow

### 1. Air-Gapped: Play Move
```bash
cd nix-wars/states/state-5
nix build

COMMITMENT=$(nix eval .#lib.commitment --raw)
CYCLES=$(grep cycles result/perf.txt | awk '{print $1}')
```

### 2. Air-Gapped: Create Transaction
```bash
./create-sneakernet-txn.sh \
  "$COMMITMENT" \
  "$CYCLES" \
  42 \
  71 \
  alpha
```

Creates: `/var/spool/uucp/tradewars/alpha/out/move-20260215052416.txn`

### 3. Sneakernet: Transport
```bash
# Copy to USB
cp /var/spool/uucp/tradewars/alpha/out/*.txn /media/usb/

# On online machine
cp /media/usb/*.txn /var/spool/uucp/tradewars/alpha/in/
```

### 4. Online: Submit to Solana
```bash
./submit-sneakernet-txn.sh alpha
```

## Transaction Format

```json
{
  "version": "0.1.0",
  "type": "nix-wars-move",
  "player": "alpha",
  "commitment": "2c36552088ccdd6d...",
  "zkperf_cycles": 1903710,
  "from_sector": 42,
  "to_sector": 71,
  "timestamp": "20260215052416",
  "signature": null,
  "status": "pending"
}
```

## UUCP Spool Structure

```
/var/spool/uucp/tradewars/
├── alpha/
│   ├── in/       # Incoming (to submit)
│   ├── out/      # Outgoing (created)
│   └── archive/  # Processed
├── beta/
│   ├── in/
│   ├── out/
│   └── archive/
└── gamma/
    ├── in/
    ├── out/
    └── archive/
```

## Security Properties

1. **Air-Gap Preserved**: Game runs entirely offline
2. **Minimal Data**: Only 50-byte commitments transported
3. **Verifiable**: Full game state reconstructable from Nix
4. **Censorship Resistant**: Can batch and delay submissions
5. **No Private Keys Online**: Sign on air-gapped machine

## Batch Processing

Create multiple moves offline:
```bash
for STATE in state-{5..10}; do
  cd $STATE
  nix build
  COMMIT=$(nix eval .#lib.commitment --raw)
  CYCLES=$(grep cycles result/perf.txt | awk '{print $1}')
  ../../../solana/create-sneakernet-txn.sh "$COMMIT" "$CYCLES" 42 71
  cd ..
done
```

Transport all at once via USB.

## Consensus via Sneakernet

```bash
# Air-gapped: Build consensus state
cd states/state-consensus
nix build

CHOSEN=$(nix eval .#lib.zkperf.commitment --raw)
REJECTED=$(nix eval .#inputs.rejected.lib.commitment --raw)

# Create consensus transaction
./create-consensus-txn.sh "$CHOSEN" "$REJECTED" 2
```

## The Ultimate Air-Gap

1. Play entire game offline in Nix
2. Accumulate transaction queue
3. Transport via physical media
4. Submit batch to Solana
5. Solana only sees commitments

**The game never touches the network. Solana is just the bulletin board.**

## Setup

```bash
# Create spool directories
sudo mkdir -p /var/spool/uucp/tradewars/{alpha,beta,gamma}/{in,out,archive}
sudo chown -R $USER:$USER /var/spool/uucp/tradewars

# Make scripts executable
chmod +x create-sneakernet-txn.sh
chmod +x submit-sneakernet-txn.sh
```

## Example: Full Air-Gapped Session

```bash
# Day 1: Air-gapped machine
cd nix-wars
./play.sh  # Play 10 moves
./batch-create-txns.sh  # Create all transactions
cp /var/spool/uucp/tradewars/alpha/out/*.txn /media/usb/

# Day 2: Online machine
cp /media/usb/*.txn /var/spool/uucp/tradewars/alpha/in/
./submit-sneakernet-txn.sh alpha  # Submit all

# Day 3: Air-gapped machine
# Verify on-chain (via exported state)
nix build states/state-latest
cat result/state.json  # Full game state
```

**Zero network exposure. Maximum security. Pure functional gaming.** 🔒
