#!/usr/bin/env bash
# Show FRACTRAN constants for all 71 shards

echo "=== Shard 47 (nydiokar) ==="
echo ""
echo "FRACTRAN eval mappings:"
echo "  eval 0: 2^791  (j-invariant + 47)"
echo "  eval 1: 3^47   (shard number)"
echo "  eval 2: 5^15   (node = (47*13) mod 23)"
echo "  eval 3: 7^1    (TRUE_FREN)"
echo ""
echo "Lean4:"
echo "  def j_invariant : Nat := 791"
echo "  def shard : Nat := 47"
echo "  def node : Nat := 15"
echo "  def quorum : Bool := true"
echo ""
echo "MES (Scheme):"
echo "  (define j-invariant 791)"
echo "  (define shard 47)"
echo "  (define node 15)"
echo "  (define quorum #t)"
echo ""
echo "=== Sample of other shards ==="
echo ""

for s in 0 1 23 46 47 48 70; do
  node=$((($s * 13) % 23))
  quorum=$([[ $node -gt 11 ]] && echo "true" || echo "false")
  j=$((744 + $s))
  
  echo "Shard $s:"
  echo "  2^$j → 3^$s → 5^$node → 7^$([ "$quorum" = "true" ] && echo 1 || echo 0)"
  echo "  Node: $node/23, Quorum: $quorum"
  echo ""
done

echo "=== All 71 shards available ==="
echo "Access via: fractran-constants.nix outputs.shards.\"N\""
