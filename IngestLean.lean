import Lean
import Std.Data.HashMap

open Lean System IO

structure LeanFileInfo where
  path : String
  lines : Nat
  hasTheorem : Bool
  hasDef : Bool
  hasInductive : Bool
deriving Repr

def analyzeLine (line : String) : (Bool × Bool × Bool) :=
  let hasThm := line.contains "theorem"
  let hasDef := line.contains "def"
  let hasInd := line.contains "inductive"
  (hasThm, hasDef, hasInd)

def analyzeFile (path : String) : IO (Option LeanFileInfo) := do
  if !(← FilePath.pathExists path) then return none
  try
    let content ← IO.FS.readFile path
    let lines := content.splitOn "\n"
    let mut hasThm := false
    let mut hasDef := false
    let mut hasInd := false
    
    for line in lines do
      let (t, d, i) := analyzeLine line
      hasThm := hasThm || t
      hasDef := hasDef || d
      hasInd := hasInd || i
    
    return some {
      path := path
      lines := lines.length
      hasTheorem := hasThm
      hasDef := hasDef
      hasInductive := hasInd
    }
  catch _ =>
    return none

def main : IO Unit := do
  let inputPath := "/home/mdupont/introspector/.temp-find-lean.txt"
  let outputPath := "/home/mdupont/introspector/lean_ingested.json"
  
  IO.println s!"📖 Reading {inputPath}..."
  let content ← IO.FS.readFile inputPath
  let allPaths := content.splitOn "\n" |>.filter (·.endsWith ".lean")
  
  IO.println s!"Found {allPaths.length} Lean files"
  
  let mut results : Array LeanFileInfo := #[]
  let mut count := 0
  let mut totalLines := 0
  let mut withThm := 0
  let mut withDef := 0
  let mut withInd := 0
  
  for path in allPaths do
    count := count + 1
    if count % 100 == 0 then
      IO.println s!"  {count}/{allPaths.length}..."
    
    match ← analyzeFile path with
    | some info =>
      results := results.push info
      totalLines := totalLines + info.lines
      if info.hasTheorem then withThm := withThm + 1
      if info.hasDef then withDef := withDef + 1
      if info.hasInductive then withInd := withInd + 1
    | none => pure ()
  
  IO.println s!"\n✅ Ingested {results.size} files"
  IO.println s!"   Lines: {totalLines}"
  IO.println s!"   Theorems: {withThm}"
  IO.println s!"   Defs: {withDef}"
  IO.println s!"   Inductives: {withInd}"
  
  let json := results.foldl (init := "[") fun acc info =>
    acc ++ "\n  {\"path\":\"" ++ info.path ++ "\",\"lines\":" ++ toString info.lines ++ ",\"theorem\":" ++ toString info.hasTheorem ++ ",\"def\":" ++ toString info.hasDef ++ ",\"inductive\":" ++ toString info.hasInductive ++ "},"
  let json := json.dropRight 1 ++ "\n]"
  
  IO.FS.writeFile outputPath json
  IO.println s!"💾 {outputPath}"
