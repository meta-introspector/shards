#!/usr/bin/env bash
set -euo pipefail

SHARD_DIR="../../shard2"
PERF_DIR="$SHARD_DIR/data/perf"
mkdir -p "$PERF_DIR"

echo "Recording pipelight build with perf (all registers)..."

cd ../pipelight

perf record \
  --call-graph dwarf \
  --all-user \
  --sample-cpu \
  --sample-regs-user=AX,BX,CX,DX,SI,DI,BP,SP,IP,FLAGS,R8,R9,R10,R11,R12,R13,R14,R15 \
  --output="$PERF_DIR/pipelight-build.perf.data" \
  -- nix build .#

echo "Generating perf report..."
perf report \
  --input="$PERF_DIR/pipelight-build.perf.data" \
  --stdio \
  > "$PERF_DIR/pipelight-build.report.txt"

echo "Generating perf script..."
perf script \
  --input="$PERF_DIR/pipelight-build.perf.data" \
  > "$PERF_DIR/pipelight-build.script.txt"

echo "Extracting register samples..."
perf script \
  --input="$PERF_DIR/pipelight-build.perf.data" \
  --fields comm,pid,tid,time,event,ip,sym,dso,addr,regs \
  > "$PERF_DIR/pipelight-build.regs.txt"

echo "Done! Results in $PERF_DIR"
