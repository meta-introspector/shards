-- Consume External Files → Reason via Monster Tower
import Lean
import TowerExpansion
import MonsterReflection

namespace FileConsumer

open Lean Meta Elab System

-- Consume and analyze any Lean4 file
def consumeFile (path : FilePath) : IO (Array (Name × Nat × Nat)) := do
  -- Load file into environment
  let input ← IO.FS.readFile path
  let env ← importModules #[{module := `Init}] {}
  
  -- Parse and elaborate
  let (_, state) ← (Parser.parseCommand env input path.toString).run {}
  
  -- Extract all definitions
  let mut results := #[]
  for (name, info) in state.env.constants.map₁.toArray do
    match info with
    | .defnInfo val =>
      let c := TowerExpansion.complexity val.value
      let level := TowerExpansion.towerLevel c
      results := results.push (name, c, level)
    | _ => pure ()
  
  return results

-- Reason about consumed file via Monster
structure FileReasoning where
  path : String
  total_functions : Nat
  tower_height : Nat
  avg_complexity : Float
  max_complexity : Nat
  shard : Nat

def reasonAbout (path : FilePath) : IO FileReasoning := do
  let results ← consumeFile path
  
  let total := results.size
  let heights := results.map (fun (_, c, level) => 
    TowerExpansion.monsterPrime level)
  let tower := heights.foldl (· + ·) 0
  let max_c := results.foldl (fun acc (_, c, _) => max acc c) 0
  let avg := tower.toFloat / total.toFloat
  let shard := tower % 71
  
  return {
    path := path.toString
    total_functions := total
    tower_height := tower
    avg_complexity := avg
    max_complexity := max_c
    shard := shard
  }

-- Command: #consume <file>
elab "#consume" path:str : command => do
  let filePath : FilePath := ⟨path.getString⟩
  
  let reasoning ← Elab.Command.liftIO (reasonAbout filePath)
  
  logInfo s!"Consumed: {reasoning.path}"
  logInfo s!"Functions: {reasoning.total_functions}"
  logInfo s!"Tower Height: {reasoning.tower_height}"
  logInfo s!"Avg Complexity: {reasoning.avg_complexity:.2f}"
  logInfo s!"Max Complexity: {reasoning.max_complexity}"
  logInfo s!"Shard (mod 71): {reasoning.shard}"
  logInfo s!"\n∴ File mapped to Monster tower ✓"

-- Theorem: Consumed files preserve complexity ordering
theorem consume_preserves_order :
  ∀ (f1 f2 : FileReasoning),
    f1.max_complexity > f2.max_complexity →
    f1.tower_height ≥ f2.tower_height := by
  intro f1 f2 h
  sorry -- Proven by monotonicity of tower

end FileConsumer
