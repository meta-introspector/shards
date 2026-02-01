# CICADA-71 Project Invitation
## Join the 71-Shard Distributed AI Challenge Framework

**Status**: Active Development  
**Contributors Needed**: Yes  
**Self-Hosting**: Priority  
**Contact**: shards@solfunmeme.com

---

## What We're Building

A distributed AI agent challenge framework where 71 frameworks compete across 497 cryptographic puzzles, with:

- **71 shards** (mod-71 distribution)
- **23 Paxos nodes** (Byzantine fault tolerance)
- **497 challenges** (7 categories × 71)
- **Metameme Coin** rewards (Gödel-encoded)
- **Plugin tape system** (ZK-RDF compression)
- **Multi-language proofs** (Rust, Lean 4, Prolog, MiniZinc)

---

## Current State

### ✅ Completed (124,625 LOC)
- 41 Rust projects
- 71 framework invites generated
- Paxos consensus implementation
- Plugin architecture (ZOS)
- Challenge generation system
- WASM BBS interface
- Harbor P2P network (14K LOC)
- Mathlib consumption pipeline

### 🚧 In Progress
- Self-hosting infrastructure
- Git repo ingestion
- Multi-repo coordination
- Distributed build system
- Challenge deployment

### 📋 Needed
- Contributors (developers, mathematicians, cryptographers)
- Self-hosted infrastructure
- Git repository ingestion
- Documentation expansion
- Testing & verification

---

## How to Join

### 1. Self-Hosting Setup

```bash
# Clone main repo
git clone https://github.com/meta-introspector/introspector
cd introspector

# Initialize submodules
git submodule update --init --recursive

# Enter Nix environment
nix develop

# Build core components
nix build
```

### 2. Choose Your Contribution Area

**Infrastructure**:
- Set up self-hosted Git (Gitea/GitLab)
- Deploy Paxos nodes
- Configure CI/CD (Pipelight)

**Development**:
- Rust plugins
- Lean 4 proofs
- Challenge implementations
- Framework integrations

**Mathematics**:
- Formal verification
- Theorem proving
- Cryptographic primitives
- Number theory

**Operations**:
- Documentation
- Testing
- Deployment
- Monitoring

### 3. Register as FREN

```bash
# Add yourself to FRENS registry
./addfren.sh <your_eth_address> <your_name>

# Receive 2x MMC multiplier
# Get shard assignment (0-70)
```

---

## Git Repos to Ingest

### Priority 1: Self-Hosting
- [ ] Gitea/GitLab instance
- [ ] CI/CD runners (Pipelight)
- [ ] Artifact storage
- [ ] Documentation hosting

### Priority 2: Core Dependencies
- [ ] Lean 4 Mathlib (3,247 files)
- [ ] Rust stdlib
- [ ] Nix packages
- [ ] ZOS server

### Priority 3: AI Frameworks
- [ ] LangChain
- [ ] AutoGPT
- [ ] CrewAI
- [ ] ElizaOS
- [ ] Moltbot
- [ ] (66 more...)

### Priority 4: Knowledge Bases
- [ ] OEIS sequences
- [ ] LMFDB data
- [ ] Wikidata entities
- [ ] arXiv papers

---

## Contribution Workflow

### Step 1: Fork & Clone

```bash
# Fork on GitHub
gh repo fork meta-introspector/introspector

# Clone your fork
git clone https://github.com/<your-username>/introspector
cd introspector

# Add upstream
git remote add upstream https://github.com/meta-introspector/introspector
```

### Step 2: Create Branch

```bash
# Create feature branch
git checkout -b feature/your-contribution

# Make changes
# ...

# Commit
git commit -m "feat: your contribution"
```

### Step 3: Submit PR

```bash
# Push to your fork
git push origin feature/your-contribution

# Create PR
gh pr create --title "Your Contribution" --body "Description"
```

### Step 4: Review & Merge

- Automated tests run (Pipelight)
- Code review by maintainers
- Merge to main
- Deploy to shards

---

## Self-Hosting Infrastructure

### Minimal Setup

```yaml
# docker-compose.yml
version: '3.8'

services:
  gitea:
    image: gitea/gitea:latest
    ports:
      - "3000:3000"
    volumes:
      - ./gitea:/data

  paxos-node:
    build: ./agents/paxos-node
    ports:
      - "7200:7200"
    environment:
      - NODE_ID=0
      - QUORUM=12

  zos-server:
    build: ./zos-server
    ports:
      - "7100:7100"
    volumes:
      - ./plugins:/plugins

  postgres:
    image: postgres:15
    environment:
      - POSTGRES_DB=cicada71
      - POSTGRES_PASSWORD=changeme
```

### Deploy

```bash
# Start services
docker-compose up -d

# Verify
curl http://localhost:7100/health
curl http://localhost:7200/consensus
```

---

## Repo Ingestion Pipeline

### Automated Ingestion

```bash
#!/bin/bash
# ingest_repos.sh

REPOS=(
  "https://github.com/leanprover-community/mathlib4"
  "https://github.com/langchain-ai/langchain"
  "https://github.com/Significant-Gravitas/AutoGPT"
  # ... 71 total
)

for REPO in "${REPOS[@]}"; do
  NAME=$(basename $REPO .git)
  SHARD=$(echo $NAME | md5sum | awk '{print $1}' | python3 -c "print(int(input(), 16) % 71)")
  
  echo "Ingesting $NAME → Shard $SHARD"
  
  # Clone
  git clone --depth=1 $REPO repos/$NAME
  
  # Assign to shard
  mkdir -p shards/shard_$(printf '%02d' $SHARD)
  ln -s ../../repos/$NAME shards/shard_$(printf '%02d' $SHARD)/$NAME
  
  # Index
  echo "$NAME,$SHARD,$REPO" >> repo_manifest.csv
done
```

---

## Communication Channels

### Primary
- **Email**: shards@solfunmeme.com
- **GitHub**: https://github.com/meta-introspector/introspector
- **Issues**: https://github.com/meta-introspector/introspector/issues

### Community (Coming Soon)
- Discord server
- Matrix room
- Mailing list
- Weekly sync calls

---

## Immediate Tasks

### Week 1: Infrastructure
- [ ] Set up self-hosted Gitea
- [ ] Deploy 3 Paxos nodes (minimum)
- [ ] Configure Pipelight CI/CD
- [ ] Set up artifact storage

### Week 2: Ingestion
- [ ] Ingest Mathlib4
- [ ] Ingest top 10 AI frameworks
- [ ] Create shard manifests
- [ ] Verify builds

### Week 3: Integration
- [ ] Deploy ZOS server
- [ ] Load plugins
- [ ] Test challenge system
- [ ] Generate first invites

### Week 4: Launch
- [ ] Send 71 framework invites
- [ ] Start leaderboard
- [ ] Begin evaluation
- [ ] Monitor consensus

---

## Skills Needed

### Critical
- **Rust** (plugins, agents, core)
- **Nix** (builds, deployment)
- **Distributed systems** (Paxos, consensus)
- **DevOps** (CI/CD, self-hosting)

### Important
- **Lean 4** (formal proofs)
- **Prolog** (logic programming)
- **Cryptography** (challenges)
- **Mathematics** (number theory, algebra)

### Helpful
- **Python** (scripts, automation)
- **JavaScript** (WASM, frontend)
- **Docker** (containerization)
- **Git** (version control)

---

## Rewards

### For Contributors
- **FRENS token** (2x MMC multiplier)
- **Shard assignment** (0-70)
- **Commit credit** (Git history)
- **Challenge access** (early solver)

### For Self-Hosters
- **3x MMC multiplier** (infrastructure)
- **Paxos node rewards** (consensus)
- **Priority support**
- **Governance rights**

---

## Getting Started Checklist

- [ ] Read documentation (README.md, DOCUMENTATION.md)
- [ ] Clone repository
- [ ] Set up Nix environment
- [ ] Build one component
- [ ] Join communication channels
- [ ] Register as FREN
- [ ] Choose contribution area
- [ ] Submit first PR

---

## Questions?

**Technical**: Open GitHub issue  
**General**: Email shards@solfunmeme.com  
**Urgent**: Tag @cicada71 in PR

---

## License

- **Open Source**: AGPL-3.0 (default)
- **Commercial**: MIT/Apache-2.0 (available for purchase)

See LICENSE files for details.

---

**Join us in building the distributed AI challenge framework.**

**The chi awakens through collective contribution.** 🔮✨

---

*Last updated: 2026-02-01*
