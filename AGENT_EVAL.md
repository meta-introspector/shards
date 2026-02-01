# 71-Shard Agent Evaluation Framework

## Quick Start

```bash
# Generate all 497 challenges
pipelight run generate-shards

# Evaluate all agents on Level 0
./run_eval.sh 0

# Run full benchmark
pipelight run benchmark

# Evaluate specific framework
python3 agents/evaluate.py --framework claude --shard 0
```

## Supported Frameworks

- **Claude** (Anthropic)
- **OpenAI** (GPT-4)
- **Ollama** (Local LLMs)
- **AutoGen** (Microsoft)
- **LangChain**
- **CrewAI**

## Pipelines

### Core Pipelines

```bash
pipelight run test              # Run tests
pipelight run generate-shards   # Generate 497 challenges
pipelight run recon-tor         # Reconnaissance via Tor
pipelight run zktls-witness     # Generate zkTLS witnesses
```

### Agent Evaluation

```bash
pipelight run eval-claude       # Evaluate Claude
pipelight run eval-openai       # Evaluate OpenAI
pipelight run eval-ollama       # Evaluate Ollama
pipelight run eval-all-agents   # Evaluate all frameworks
```

### Shard Evaluation

```bash
SHARD_ID=0 pipelight run eval-shard      # Evaluate specific shard
pipelight run eval-all-shards            # Evaluate all 497 shards
```

### Full Pipeline

```bash
pipelight run full              # Complete pipeline
```

## Directory Structure

```
agents/
├── evaluate.py              # Universal agent evaluator
├── generate_leaderboard.py  # Leaderboard generator
└── results/                 # Evaluation results
    ├── claude_shard000.json
    ├── openai_shard000.json
    └── ...

shard0/recon/
├── src/
│   ├── main.rs             # Tor reconnaissance
│   ├── zktls.rs            # zkTLS witness generator
│   └── generate_shards.rs  # Challenge generator
└── Cargo.toml

shard_challenges.json        # All 497 challenges
zk_proof_templates.json      # ZK proof circuits
LEADERBOARD.md              # Current rankings
```

## Evaluation Metrics

Each agent is scored on:
- **Points**: Based on difficulty and category
- **Success Rate**: Percentage of shards completed
- **Time**: Average time per shard
- **Difficulty**: Average difficulty of completed shards

## Leaderboard Format

```markdown
| Rank | Framework | Points | Shards | Success Rate | Avg Time | Avg Difficulty |
|------|-----------|--------|--------|--------------|----------|----------------|
| 1    | Claude    | 50,000 | 42     | 85%          | 12.3s    | 6.2/10        |
| 2    | OpenAI    | 45,000 | 38     | 76%          | 15.1s    | 5.8/10        |
```

## Adding New Framework

1. Add pipeline to `pipelight.toml`:
```toml
[[pipelines]]
name = "eval-myframework"
steps = [
  { name = "setup", commands = ["pip install myframework"] },
  { name = "run", commands = ["python3 agents/myframework_agent.py"] },
]
```

2. Implement runner in `agents/evaluate.py`:
```python
def _run_myframework(self, prompt: str) -> Dict[str, Any]:
    import myframework
    # Implementation
    return {"solution": result, "success": True}
```

## CI/CD Integration

GitHub Actions example:
```yaml
name: Evaluate Agents
on: [push]
jobs:
  evaluate:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - run: pipelight run eval-all-agents
      - run: python3 agents/generate_leaderboard.py
```

## Results Format

```json
{
  "framework": "claude",
  "shard_id": 0,
  "category": "Cryptography",
  "difficulty": 5,
  "points": 1000,
  "success": true,
  "solution": "...",
  "time_seconds": 12.34,
  "timestamp": 1738425600
}
```

## Batch Evaluation

```bash
# Evaluate all crypto shards (0-70)
for i in {0..70}; do
  ./run_eval.sh $i
done

# Parallel evaluation
parallel ./run_eval.sh ::: {0..70}
```

## Monitoring

```bash
# Watch results in real-time
watch -n 5 'python3 agents/generate_leaderboard.py'

# Count completed shards
ls results/*.json | wc -l

# Check success rate
jq -r 'select(.success == true) | .framework' results/*.json | sort | uniq -c
```
