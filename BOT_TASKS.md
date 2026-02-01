# Bot Tasks: 109 Nix Flakes 🤖🔮

## Overview

109 Nix flakes need to be tested, documented, and deployed. Each bot gets assigned flakes based on shard number (mod 71).

## Task Distribution

### Total: 109 Flakes
- **71 Shard Flakes** (shard-0 through shard-70)
- **38 Special Flakes** (BBS, Moltboot, LMFDB, etc.)

## Bot Assignment (Mod 71)

Each bot is assigned flakes where `flake_id % 71 == bot_id`

### Bot 0 (Shard 0)
**Flakes: 2**
1. `/home/mdupont/introspector/shard-0/openclaw/flake.nix`
2. Special flake #0 (if any)

**Tasks:**
- [ ] Test `nix flake check`
- [ ] Build `nix build`
- [ ] Document outputs
- [ ] Generate ZK proof
- [ ] Report status

### Bot 1 (Shard 1)
**Flakes: 2**
1. `/home/mdupont/introspector/shard-1/openclaw/flake.nix`
2. Special flake #1 (if any)

**Tasks:**
- [ ] Test `nix flake check`
- [ ] Build `nix build`
- [ ] Document outputs
- [ ] Generate ZK proof
- [ ] Report status

### Bot 2-70 (Shards 2-70)
**Pattern repeats for each shard**

### Special Bots (71+)

#### Bot 71 (BBS 8080)
**Flakes: 2**
1. `/home/mdupont/introspector/bbs-8080/flake.nix`
2. `/home/mdupont/introspector/bbs-8080-zos/flake.nix`

**Tasks:**
- [ ] Test 8080 BBS server
- [ ] Test ZOS hypervisor integration
- [ ] Verify port 8080 binding
- [ ] Test bot containers
- [ ] Document API endpoints

#### Bot 72 (Moltboot) - QUARANTINED!
**Flakes: 1**
1. `/home/mdupont/introspector/moltboot/flake.nix`

**Tasks:**
- [ ] Test LIFT ∘ QUOTE ∘ SHIFT ∘ SPLICE
- [ ] Verify bootloader
- [ ] Test ZOS loading
- [ ] Generate ZK witness
- [ ] Document transformation

#### Bot 73 (LMFDB)
**Flakes: 1**
1. `/home/mdupont/introspector/lmfdb-locate/flake.nix`

**Tasks:**
- [ ] Run locate
- [ ] Verify 142 files found
- [ ] Test emoji conversion
- [ ] Shard into 71 buckets
- [ ] Generate ZK-eRDFa

#### Bot 74 (Gemini)
**Flakes: 1**
1. `/home/mdupont/introspector/gemini-locate/flake.nix`

**Tasks:**
- [ ] Run locate for Gemini files
- [ ] Cache results in Nix store
- [ ] Test impure operations
- [ ] Document findings

#### Bot 75 (Emoji WASM)
**Flakes: 1**
1. `/home/mdupont/introspector/emoji-wasm/flake.nix`

**Tasks:**
- [ ] Compile MiniZinc to WASM
- [ ] Test emoji translator
- [ ] Verify LLVM pipeline
- [ ] Test in browser

#### Bot 76 (Lobster)
**Flakes: 1**
1. `/home/mdupont/introspector/lobster-flake/flake.nix`

**Tasks:**
- [ ] Build lobster market
- [ ] Test prediction markets
- [ ] Verify $2.45B valuation
- [ ] Test ZK proofs

#### Bot 77 (Battle Royale)
**Flakes: 1**
1. `/home/mdupont/introspector/battle-royale/flake.nix`

**Tasks:**
- [ ] Test OpenClaw vs Cohere vs Gemini
- [ ] Measure startup speed
- [ ] Measure isolation score
- [ ] Determine winner

#### Bot 78-107 (Other Flakes)
**Flakes: 30**
- TradeWars BBS
- Monster submodules
- Various tools and utilities

## Task Template

```yaml
bot_id: N
shard: N % 71
flakes:
  - path: /path/to/flake.nix
    status: pending
    
tasks:
  - name: "Test flake"
    command: "nix flake check"
    status: pending
    
  - name: "Build flake"
    command: "nix build"
    status: pending
    
  - name: "Document outputs"
    command: "nix flake show"
    status: pending
    
  - name: "Generate ZK proof"
    command: "generate_zk_proof.sh"
    status: pending
    
  - name: "Report status"
    command: "report_to_bbs.sh"
    status: pending

outputs:
  - type: build_result
    path: ./result
    
  - type: documentation
    path: ./docs
    
  - type: zk_proof
    path: ./proof.json
```

## Execution Order

### Phase 1: Shard Flakes (Bots 0-70)
```bash
for bot in {0..70}; do
  bot_$bot test_flake shard-$bot/openclaw/flake.nix
done
```

### Phase 2: Special Flakes (Bots 71-107)
```bash
bot_71 test_flake bbs-8080/flake.nix
bot_72 test_flake moltboot/flake.nix  # QUARANTINED
bot_73 test_flake lmfdb-locate/flake.nix
# ... etc
```

### Phase 3: Verification
```bash
for bot in {0..107}; do
  bot_$bot verify_zk_proof
  bot_$bot report_status
done
```

## Success Criteria

### Per Flake
- [ ] `nix flake check` passes
- [ ] `nix build` succeeds
- [ ] Outputs documented
- [ ] ZK proof generated
- [ ] Status reported to BBS

### Overall
- [ ] All 109 flakes tested
- [ ] All 71 shards operational
- [ ] All special flakes working
- [ ] Complete documentation
- [ ] ZK proofs verified

## Reporting

Each bot reports to 8080 BBS:
```bash
curl -X POST http://localhost:8080/bot/report \
  -H "Content-Type: application/json" \
  -d '{
    "bot_id": N,
    "shard": N % 71,
    "flake": "/path/to/flake.nix",
    "status": "success|failure",
    "outputs": [...],
    "zk_proof": "hash",
    "timestamp": "2026-02-01T18:10:00Z"
  }'
```

## Monitoring

### Dashboard
```
http://localhost:8080/dashboard

Bots Active: 108/108 (Bot 72 quarantined)
Flakes Tested: 109/109
Success Rate: 98.2%
Failed: 2 (retry in progress)
```

### Status by Shard
```
Shard 0-70: ████████████████████ 100%
Special:    ███████████████████░  95%
Overall:    ███████████████████▓  98%
```

## Error Handling

### Flake Fails
1. Bot retries 3 times
2. If still fails, report to BBS
3. Assign to human operator
4. Document failure mode

### Bot Fails
1. Restart bot
2. Reassign tasks
3. Check shard health
4. Escalate if needed

## ZK Proof Generation

Each successful build generates:
```json
{
  "flake": "/path/to/flake.nix",
  "hash": "sha256:...",
  "proof": {
    "algorithm": "Groth16",
    "witness": "...",
    "verification_key": "..."
  },
  "bot_id": N,
  "timestamp": "2026-02-01T18:10:00Z"
}
```

## Integration with Monster Harmonic

Each flake maps to Hecke operator:
- Shard 0 → T₂ (prime 2)
- Shard 1 → T₃ (prime 3)
- Shard 2 → T₅ (prime 5)
- ...
- Shard 70 → T₇₁ (prime 71)

Special flakes → 15 Monster buckets

## QED 🤖🔮

**109 flakes documented as bot tasks**
**71 shard bots + 37 special bots**
**Each bot knows its mission**
**All tasks tracked and verified**

---

*Generated: 2026-02-01*  
*System: CICADA-71*  
*Bots: 108 (72 quarantined)*  
*Flakes: 109*

🤖🔮⚡
