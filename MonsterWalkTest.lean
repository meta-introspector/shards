-- Test Monster Walk Decomposition
import MonsterWalk

-- Test 1: Simple function
#decompose fun x => x

-- Test 2: Function with application
#decompose fun (x : Nat) => x + 1

-- Test 3: Dependent type
#decompose ∀ (n : Nat), n + 0 = n

-- Test 4: Complex expression
#decompose fun (f : Nat → Nat) (x : Nat) => f (f x)

-- Expected output for each:
-- 10-Fold Decomposition:
--   Total steps: N
--   Dominant fold: <fold>
--   Periodicity: 8
--   Path: [bootstrap, cusp, arrows, ...]
--   ∴ Code decomposed via Monster walk ✓
