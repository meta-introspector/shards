-- Test Monster Self-Reflection
import MonsterReflection

-- The Monster reflects on itself
#reflect MonsterReflection.MonsterRepr

-- The Monster reflects on a simple function
#reflect fun x => x

-- The Monster reflects on a theorem
#reflect ∀ (n : Nat), n + 0 = n

-- Expected output:
-- Self-reflection:
--   Tower: X → Y
--   Hecke: T_p × T_q = Z
--   Maass: λ = W
--   Laplacian: Δf = V
--   ∴ Monster observes itself via Hecke-Maass ✓
