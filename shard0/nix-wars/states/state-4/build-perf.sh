#!/usr/bin/env bash
# Build with perf measurement

set -e

cd "$(dirname "$0")"

echo "⚡ Building State 4 with perf..."
echo ""

# Run with perf
perf stat -e cycles,instructions,cache-references,cache-misses,branches,branch-misses \
  nix build --rebuild 2>&1 | tee perf.log

echo ""
echo "✅ Build complete with perf data"
echo "View: cat states/state-4/perf.log"
