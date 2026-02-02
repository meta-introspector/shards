-- Tower Expansion: All Lean4 Functions → Increasing Complexity
import Lean

namespace TowerExpansion

open Lean Meta Elab

-- Complexity measure for any Lean4 function
def complexity (e : Expr) : Nat :=
  match e with
  | .bvar _ => 1
  | .sort _ => 1
  | .const _ _ => 1
  | .app fn arg => 1 + complexity fn + complexity arg
  | .lam _ ty body _ => 2 + complexity ty + complexity body
  | .forallE _ ty body _ => 2 + complexity ty + complexity body
  | .letE _ ty val body _ => 3 + complexity ty + complexity val + complexity body
  | .mdata _ e => complexity e
  | .proj _ _ e => 1 + complexity e
  | _ => 0

-- Tower level (log scale)
def towerLevel (c : Nat) : Nat :=
  if c ≤ 1 then 0
  else if c ≤ 10 then 1
  else if c ≤ 100 then 2
  else if c ≤ 1000 then 3
  else 4

-- Monster prime for complexity
def monsterPrime (level : Nat) : Nat :=
  match level with
  | 0 => 2   -- Bootstrap
  | 1 => 13  -- Simple
  | 2 => 47  -- Medium
  | 3 => 71  -- Complex (cusp)
  | _ => 71  -- Very complex (cusp)

-- Expand tower: collect all functions in environment
def expandTower : MetaM (Array (Name × Nat × Nat)) := do
  let env ← getEnv
  let mut tower := #[]
  
  for (name, info) in env.constants.map₁.toArray do
    match info with
    | .defnInfo val =>
      let c := complexity val.value
      let level := towerLevel c
      tower := tower.push (name, c, level)
    | .thmInfo val =>
      let c := complexity val.value
      let level := towerLevel c
      tower := tower.push (name, c, level)
    | _ => pure ()
  
  return tower.qsort (fun a b => a.2.1 < b.2.1)

-- Show tower with increasing complexity
elab "#tower" : command => do
  let tower ← Elab.Command.liftTermElabM expandTower
  
  logInfo s!"Tower Expansion: {tower.size} functions"
  logInfo s!"\nComplexity Distribution:"
  
  let mut level_counts := #[0, 0, 0, 0, 0]
  for (_, _, level) in tower do
    if level < 5 then
      level_counts := level_counts.set! level (level_counts[level]! + 1)
  
  logInfo s!"  Level 0 (≤1):    {level_counts[0]!} functions → GF(2)"
  logInfo s!"  Level 1 (≤10):   {level_counts[1]!} functions → GF(13)"
  logInfo s!"  Level 2 (≤100):  {level_counts[2]!} functions → GF(47)"
  logInfo s!"  Level 3 (≤1000): {level_counts[3]!} functions → GF(71)"
  logInfo s!"  Level 4 (>1000): {level_counts[4]!} functions → GF(71)"
  
  logInfo s!"\nTop 10 Most Complex:"
  for i in [0:min 10 tower.size] do
    let (name, c, level) := tower[tower.size - 1 - i]!
    logInfo s!"  {name}: complexity {c} (level {level})"

-- Theorem: Complexity is monotonic
theorem complexity_monotonic :
  ∀ (e1 e2 : Expr), complexity (.app e1 e2) > complexity e1 := by
  intro e1 e2
  simp [complexity]
  omega

end TowerExpansion
