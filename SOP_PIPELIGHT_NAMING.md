# SOP: CI/CD Tool Name Disambiguation

## Correct Tool Names

### ✓ Pipelight
- **Correct**: `pipelight`
- **Command**: `pipelight run <pipeline-name>`
- **Config**: `pipelight.toml` or `pipelight.yml`
- **URL**: https://pipelight.dev

### ✗ Common Misspellings to Catch

| ❌ Wrong | ✓ Correct |
|---------|----------|
| pipelite | pipelight |
| pipeline | pipelight |
| buildpipe | pipelight |
| piplight | pipelight |

## Usage in This Project

```bash
# Correct
pipelight run fractran-apply-71

# Wrong (will fail)
pipelite run fractran-apply-71
pipeline run fractran-apply-71
buildpipe run fractran-apply-71
```

## Configuration File

**File**: `pipelight.toml` (TOML format)

```toml
[[pipelines]]
name = "fractran-apply-71"
description = "Apply FRACTRAN through Nix store 71 times"
```

## Quick Reference

- **Tool**: Pipelight
- **Binary**: `pipelight`
- **Config**: `pipelight.toml`
- **Run**: `pipelight run <name>`
- **List**: `pipelight ls`
- **Help**: `pipelight --help`

## Mnemonic

**"Pipe + Light = Pipelight"** (not lite, not line, not build)
