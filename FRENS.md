# FRENS Token Registry
## CICADA-71 Challenge Framework

Early adopters and contributors receive FRENS tokens for participation.

---

## FRENS List

### Core Contributors

**nathan**
- Address: `0x2c6cDd7e0EaDF461e27bA2fec785bB7c27CBb4BA`
- Chain: ethereum
- Email: 71@solfunmeme.com
- URL: https://etherscan.io/address/0x2c6cDd7e0EaDF461e27bA2fec785bB7c27CBb4BA
- Role: Early adopter
- Rewards: 2x MMC multiplier
- Status: Active
- Added: 2026-02-01

---

## Adding a FREN

Use the `addfren.sh` script to add FRENS with zkTLS proof:

```bash
# Add FREN with Solana token
./addfren.sh https://solscan.io/token/<TOKEN_ADDRESS>

# Schedule hourly proofs
./addfren.sh https://solscan.io/token/<TOKEN_ADDRESS> hourly

# Schedule daily proofs
./addfren.sh https://solscan.io/token/<TOKEN_ADDRESS> daily
```

---

## FRENS Token Economics

- **Early Adopters** (first 23 frameworks): 2x Metameme Coin rewards
- **Core Contributors**: 3x MMC multiplier
- **Challenge Solvers**: 1x MMC per solved shard
- **Paxos Validators**: Staking rewards from consensus

---

## Claiming Rewards

```solidity
// FRENS token claim (multi-chain)
function claimRewards(address fren, uint256 shardId) public {
    require(isFren(fren), "Not a FREN");
    uint256 multiplier = getFrenMultiplier(fren);
    uint256 reward = shardRewards[shardId] * multiplier;
    metamemeCoin.transfer(fren, reward);
}
```

---

## zkTLS Witness Format

Each FREN addition generates a zkTLS witness:

```json
{
  "timestamp": "2026-02-01T16:54:00Z",
  "token": "<TOKEN_ADDRESS>",
  "url": "https://solscan.io/token/<TOKEN_ADDRESS>",
  "schedule": "once|hourly|daily",
  "proof_exists": true,
  "phone_exists": true
}
```

---

## Supported Chains

- Solana (primary)
- Ethereum
- Base
- Arbitrum
- Optimism

---

## Contact

Submit PR or use `addfren.sh` script.

Email: shards@solfunmeme.com

**nydiokar**
- Address: `GWryBrYoBvCKKr2vR3YJxL6CWNTPxurwTq3w2dA5S2fw`
- Chain: solana
- URL: https://solscan.io/address/GWryBrYoBvCKKr2vR3YJxL6CWNTPxurwTq3w2dA5S2fw
- Role: Early adopter
- Rewards: 2x MMC multiplier
- Status: Active
- Added: 2026-02-08

**kanebra**
- Address: `26qVRWZgpAhZLy7Fkt1vUiqLFTTewVPeqRxM5sWxA9qw`
- Chain: solana
- URL: https://solscan.io/address/26qVRWZgpAhZLy7Fkt1vUiqLFTTewVPeqRxM5sWxA9qw
- Role: Early adopter
- Rewards: 2x MMC multiplier
- Status: Active
- Added: 2026-02-10
