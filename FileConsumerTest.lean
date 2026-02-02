-- Test File Consumption
import FileConsumer

-- Consume our own files
#consume "SimpleExprMonster.lean"
#consume "MetaCoqMonsterProof.lean"
#consume "TowerExpansion.lean"

-- Consume external files
#consume "TestMeta.org"

-- Expected output for each:
-- Consumed: <path>
-- Functions: N
-- Tower Height: H
-- Avg Complexity: C
-- Max Complexity: M
-- Shard (mod 71): S
-- ∴ File mapped to Monster tower ✓
