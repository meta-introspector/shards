#!/usr/bin/env bash
set -euo pipefail

echo "🔍 Analyzing Nix Store for Science Lab 🔍"
echo "========================================="
echo

# Find all science packages in nix store
echo "📦 Science Packages in Nix Store:"
echo

packages=(
  "gap" "pari" "maxima" 
  "lean" "coq" "agda" "z3" "cvc5"
  "swiProlog" "sbcl" "clojure"
  "minizinc"
  "python3" "numpy" "scipy"
  "parquet"
)

for pkg in "${packages[@]}"; do
  count=$(find /nix/store -maxdepth 1 -name "*${pkg}*" -type d 2>/dev/null | wc -l)
  if [ "$count" -gt 0 ]; then
    echo "  ✓ $pkg: $count versions"
    find /nix/store -maxdepth 1 -name "*${pkg}*" -type d 2>/dev/null | head -3 | while read dir; do
      size=$(du -sh "$dir" 2>/dev/null | cut -f1)
      echo "    - $(basename "$dir") ($size)"
    done
  else
    echo "  ✗ $pkg: not found"
  fi
done

echo
echo "📊 Parquet Files in Nix Store:"
echo

find /nix/store -name "*.parquet" -type f 2>/dev/null | while read file; do
  size=$(du -sh "$file" 2>/dev/null | cut -f1)
  echo "  - $(basename "$file") ($size)"
  echo "    Path: $file"
done

echo
echo "🔬 Parquet Tools:"
echo

# Find parquet crate
parquet_crates=$(find /nix/store -maxdepth 1 -name "*parquet*" -type d 2>/dev/null | wc -l)
echo "  Parquet crates: $parquet_crates"

# Find parquet binaries
parquet_bins=$(find /nix/store -name "*parquet*" -type f -executable 2>/dev/null | wc -l)
echo "  Parquet binaries: $parquet_bins"

echo
echo "💾 Nix Store Statistics:"
echo

store_size=$(du -sh /nix/store 2>/dev/null | cut -f1)
store_items=$(find /nix/store -maxdepth 1 -type d 2>/dev/null | wc -l)

echo "  Total size: $store_size"
echo "  Total items: $store_items"

echo
echo "∴ Nix store analysis complete ✓"
