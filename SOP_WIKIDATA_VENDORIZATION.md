# SOP: Wikidata Dataset Vendorization (Supersingular Primes Only)

## Protocol: Clone → Fork → Flake Input

### Step 1: Clone Upstream

```bash
git clone https://github.com/philippesaade/wikidata.git data/wikidata-full
git clone https://github.com/Vijaysr4/en_wikidata_5M_entities.git data/wikidata-5m
git clone https://github.com/piebro/wikidata-extraction.git data/wikidata-triples
```

### Step 2: Fork to meta-introspector

```bash
cd data/wikidata-full
gh repo fork --org meta-introspector

cd ../wikidata-5m
gh repo fork --org meta-introspector

cd ../wikidata-triples
gh repo fork --org meta-introspector
```

### Step 3: Add as Flake Inputs

```nix
inputs = {
  wikidata-full.url = "github:meta-introspector/wikidata";
  wikidata-5m.url = "github:meta-introspector/en_wikidata_5M_entities";
  wikidata-triples.url = "github:meta-introspector/wikidata-extraction";
}
```

### Step 4: Shard by Supersingular Primes

**Supersingular primes**: 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71

```
Author → mod 71
Repo   → mod 59
File   → mod 47
Line   → mod 41
Token  → mod 31
Value  → mod 29
Byte   → mod 23
Bit    → mod 19
```

### Step 5: Pipelight Jobs (3 separate)

```toml
[[pipelines]]
name = "wikidata-full-sync"
[[pipelines.steps]]
commands = ["git -C data/wikidata-full pull"]

[[pipelines]]
name = "wikidata-5m-sync"
[[pipelines.steps]]
commands = ["git -C data/wikidata-5m pull"]

[[pipelines]]
name = "wikidata-triples-sync"
[[pipelines.steps]]
commands = ["git -C data/wikidata-triples pull"]
```
