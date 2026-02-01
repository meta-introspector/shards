# MiniZinc → LLVM → WASM Emoji Optimizer

Compile MiniZinc constraint solver to WebAssembly via LLVM.

## Pipeline

```
emoji_optimization.mzn (MiniZinc)
    ↓ minizinc --compile
emoji_opt.fzn (FlatZinc)
    ↓ convert to C
emoji_opt.c (C code)
    ↓ clang -emit-llvm
emoji_opt.ll (LLVM IR)
    ↓ opt -O3
emoji_opt_opt.ll (Optimized IR)
    ↓ emcc
emoji_opt.wasm (WebAssembly)
```

## Build

```bash
nix build .#emoji-optimizer-wasm
./result/bin/emoji-optimizer
```

## Run in Browser

```bash
nix develop
python -m http.server 8000
open http://localhost:8000
```

## What It Does

1. Takes 50 emoji candidates
2. Selects best 20 by frequency
3. Ensures core emojis included: 🔮⚡🕳️🛋️🔐
4. Maximizes total frequency score
5. Runs in browser via WASM

## Tech Stack

- **MiniZinc**: Constraint programming
- **LLVM**: Intermediate representation
- **Emscripten**: LLVM → WASM compiler
- **Nix**: Reproducible builds

🔮⚡✨
