/-
Write the exact declaration graph of the compiled project.

Usage: lake env lean --run verification/decl-graph/ExactGraph.lean ROOT MODULES OUT

ROOT is the folder of the compiled files, for example `.lake/build/lib/lean`. MODULES has one
module name per line. For every constant of every listed module the script writes one line to
OUT with four columns separated by tabs: the module, the constant's name, its kind and the
names of all constants that its type and its value mention, separated by spaces.

Each module is read from its compiled parts `.olean`, `.olean.server` and `.olean.private`
together, because the private part holds the proofs of theorems and shares objects with the
other two. A module without the later parts is read from `.olean` alone. Auxiliary
constants that Lean creates, such as `_proof_1` or `match_1`, are written as well, so that a
later step can pass through them. Nothing is elaborated or imported, and no proof is checked.
-/
import Lean
open Lean

def kindOf : ConstantInfo → String
  | .thmInfo _ => "thm" | .defnInfo _ => "def" | .inductInfo _ => "ind" | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec" | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"

def uses (ci : ConstantInfo) : Array Name :=
  let fromType := ci.type.getUsedConstants
  match ci.value? (allowOpaque := true) with
  | some v =>
    let seen : Std.HashSet Name := fromType.foldl (·.insert ·) {}
    v.getUsedConstants.foldl (init := fromType) fun acc n => if seen.contains n then acc else acc.push n
  | none => fromType

def nameText (n : Name) : String := n.toString (escape := false)

/-- The lines of one module, and the memory regions that hold its compiled data. -/
unsafe def readOne (root : System.FilePath) (m : String) : IO (String × Array CompactedRegion) := do
  let base := (m.splitOn ".").foldl (· / ·) root
  -- The private part shares objects with the public and server parts, so the three are read
  -- together and in this order. The last part read holds every constant of the module.
  let mut files := #[base.addExtension "olean"]
  for ext in ["olean.server", "olean.private"] do
    let f := base.addExtension ext
    if ← f.pathExists then files := files.push f
  let parts ← readModuleDataParts files
  let some (data, _) := parts.back? | throw <| IO.userError s!"no compiled part of {m}"
  let mut lines := ""
  for ci in data.constants do
    let refs := " ".intercalate ((uses ci).map nameText).toList
    lines := lines ++ s!"{m}\t{nameText ci.name}\t{kindOf ci}\t{refs}\n"
  return (lines, parts.map (·.2))

/-- The lines of some modules. A module's regions are freed only after readOne has returned, when
nothing refers to the compiled data any more. -/
unsafe def readSome (root : System.FilePath) (mods : Array String) : IO (Array String) := do
  let mut out := #[]
  for m in mods do
    let (lines, regions) ← readOne root m
    out := out.push lines
    for r in regions.reverse do r.free
  return out

unsafe def main (args : List String) : IO Unit := do
  let [root, modsPath, outPath] := args
    | throw <| IO.userError "usage: ExactGraph.lean ROOT MODULES OUT"
  let mods := (← IO.FS.lines modsPath).filter (· ≠ "")
  let h ← IO.FS.Handle.mk outPath .write
  let workers := 4
  let batch := 2000
  let mut done := 0
  for start in [0:mods.size:batch] do
    let part := mods.extract start (start + batch)
    let mut tasks := #[]
    for w in [0:workers] do
      let mine := (Array.range part.size).filterMap fun i => if i % workers == w then part[i]? else none
      tasks := tasks.push (← IO.asTask (prio := .dedicated) (readSome root mine))
    for t in tasks do
      for lines in ← IO.ofExcept t.get do
        h.putStr lines
    h.flush
    done := done + part.size
    IO.eprintln s!"{done} of {mods.size} modules"
