# UUCP <-> Solana Gateway

**Bidirectional bridge between UUCP sneakernet and Solana blockchain**

## Architecture

```
Air-Gapped Machines          Gateway Node              Solana Network
┌─────────────────┐         ┌──────────┐             ┌─────────────┐
│ Nix-Wars Game   │         │  UUCP    │             │   Solana    │
│                 │ ──USB──>│  Spool   │──Submit────>│   RPC       │
│                 │         │          │             │             │
│                 │ <─USB───│  Export  │<──Query─────│   History   │
└─────────────────┘         └──────────┘             └─────────────┘
```

## Gateway Functions

### 1. UUCP → Solana (Incoming)
- Monitors `/var/spool/uucp/tradewars/gateway/incoming/`
- Submits transactions to Solana
- Archives with signature

### 2. Solana → UUCP (Outgoing)
- Queries recent Solana transactions
- Exports to `/var/spool/uucp/tradewars/gateway/outgoing/`
- Distributes to player spools

## Directory Structure

```
/var/spool/uucp/tradewars/gateway/
├── incoming/     # UUCP -> Solana queue
├── outgoing/     # Solana -> UUCP queue
├── processed/    # Successfully submitted
└── failed/       # Failed submissions
```

## Setup

### 1. Create Directories
```bash
sudo mkdir -p /var/spool/uucp/tradewars/gateway/{incoming,outgoing,processed,failed}
sudo chown -R uucp:uucp /var/spool/uucp/tradewars
```

### 2. Install Service
```bash
sudo cp uucp-solana-gateway.service /etc/systemd/system/
sudo systemctl daemon-reload
sudo systemctl enable uucp-solana-gateway
sudo systemctl start uucp-solana-gateway
```

### 3. Check Status
```bash
sudo systemctl status uucp-solana-gateway
sudo journalctl -u uucp-solana-gateway -f
```

## Usage

### Submit Transaction via Gateway
```bash
# Create transaction on air-gapped machine
./create-sneakernet-txn.sh <commitment> <cycles> 42 71 alpha

# Transport to gateway node
cp /var/spool/uucp/tradewars/alpha/out/*.txn /media/usb/

# On gateway node
cp /media/usb/*.txn /var/spool/uucp/tradewars/gateway/incoming/

# Gateway automatically submits to Solana
# Check processed directory for signature
ls /var/spool/uucp/tradewars/gateway/processed/
```

### Receive Transactions from Solana
```bash
# Gateway automatically exports recent transactions
ls /var/spool/uucp/tradewars/gateway/outgoing/

# Transport back to air-gapped machine
cp /var/spool/uucp/tradewars/gateway/outgoing/*.txn /media/usb/
```

## Configuration

Environment variables:
- `POLL_INTERVAL`: Seconds between gateway cycles (default: 60)

```bash
# Fast polling (10s)
sudo systemctl edit uucp-solana-gateway
# Add: Environment="POLL_INTERVAL=10"
```

## Transaction Flow

### Incoming (UUCP → Solana)
1. Transaction arrives in `incoming/`
2. Gateway reads commitment, cycles, sectors
3. Submits to Solana via Anchor
4. Receives signature
5. Moves to `processed/` with signature added
6. Or moves to `failed/` on error

### Outgoing (Solana → UUCP)
1. Gateway queries Solana transaction history
2. Filters for NixWars program transactions
3. Exports new transactions to `outgoing/`
4. Deduplicates by signature

## Monitoring

```bash
# Watch gateway logs
sudo journalctl -u uucp-solana-gateway -f

# Check queue sizes
watch -n 5 'ls /var/spool/uucp/tradewars/gateway/*/ | wc -l'

# View recent processed
ls -lt /var/spool/uucp/tradewars/gateway/processed/ | head
```

## Multi-Gateway Network

Deploy multiple gateways for redundancy:

```
Air-Gapped ──┬──> Gateway A ──┐
             │                 ├──> Solana
             └──> Gateway B ──┘
```

Each gateway independently processes transactions.

## Security

- Gateway runs as `uucp` user (limited privileges)
- No private keys stored (uses system Solana wallet)
- Transactions are commitments only (50 bytes)
- Full game state never leaves air-gapped machines

## Example: Full Cycle

```bash
# Day 1: Air-gapped machine
cd nix-wars/states/state-5
nix build
./create-sneakernet-txn.sh $(nix eval .#lib.commitment --raw) 1903710 42 71 alpha

# Day 2: Transport to gateway
cp /var/spool/uucp/tradewars/alpha/out/*.txn /media/usb/
# Physical transport to gateway node
cp /media/usb/*.txn /var/spool/uucp/tradewars/gateway/incoming/

# Gateway automatically processes (within 60s)
# Check: /var/spool/uucp/tradewars/gateway/processed/

# Day 3: Retrieve confirmations
cp /var/spool/uucp/tradewars/gateway/processed/*.txn /media/usb/
# Physical transport back
cp /media/usb/*.txn /var/spool/uucp/tradewars/alpha/in/
```

## The Bridge

UUCP is the sneakernet protocol from the 1980s.
Solana is the modern blockchain.
The gateway bridges 40 years of technology.

**Old school meets new school. Air-gap meets blockchain.** 🌉
