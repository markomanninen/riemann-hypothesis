/-
Write, for every constant of the compiled project, the constants that its type mentions.

Usage: lake env lean --run verification/decl-graph/StatementGraph.lean ROOT MODULES OUT [all]

ROOT is the folder of the compiled files, for example `.lake/build/lib/lean`. MODULES has one
module name per line. For every constant of every listed module the script writes one line to
OUT with four columns separated by tabs: the module, the constant's name, its kind and the
names of all constants that its type mentions, separated by spaces. The type of a theorem is
its statement, so the line of a theorem lists what the statement is written with and leaves
the proof out.

By default a module is read from its public part `.olean` alone, which holds the type of every
constant that other modules can see and is much smaller than the part with the proofs. In that
part a theorem has the kind `axiom`, because its proof is kept elsewhere. With the fourth
argument `all` the three parts are read together, as `ExactGraph.lean` reads them, and private
constants are written as well. Nothing is elaborated or imported, and no proof is checked.
-/
import Lean
open Lean

def kindOf : ConstantInfo → String
  | .thmInfo _ => "thm" | .defnInfo _ => "def" | .inductInfo _ => "ind" | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec" | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"

def nameText (n : Name) : String := n.toString (escape := false)

/-- The lines of one module, and the memory regions that hold its compiled data. -/
unsafe def readOne (root : System.FilePath) (all : Bool) (m : String) : IO (String × Array CompactedRegion) := do
  let base := (m.splitOn ".").foldl (· / ·) root
  let mut files := #[base.addExtension "olean"]
  if all then
    for ext in ["olean.server", "olean.private"] do
      let f := base.addExtension ext
      if ← f.pathExists then files := files.push f
  let parts ← readModuleDataParts files
  let some (data, _) := parts.back? | throw <| IO.userError s!"no compiled part of {m}"
  let mut lines := ""
  for ci in data.constants do
    let refs := " ".intercalate (ci.type.getUsedConstants.map nameText).toList
    lines := lines ++ s!"{m}\t{nameText ci.name}\t{kindOf ci}\t{refs}\n"
  return (lines, parts.map (·.2))

/-- The lines of some modules. A module's regions are freed only after readOne has returned, when
nothing refers to the compiled data any more. -/
unsafe def readSome (root : System.FilePath) (all : Bool) (mods : Array String) : IO (Array String) := do
  let mut out := #[]
  for m in mods do
    let (lines, regions) ← readOne root all m
    out := out.push lines
    for r in regions.reverse do r.free
  return out

unsafe def main (args : List String) : IO Unit := do
  let (root, modsPath, outPath, all) ← match args with
    | [root, modsPath, outPath] => pure (root, modsPath, outPath, false)
    | [root, modsPath, outPath, "all"] => pure (root, modsPath, outPath, true)
    | _ => throw <| IO.userError "usage: StatementGraph.lean ROOT MODULES OUT [all]"
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
      tasks := tasks.push (← IO.asTask (prio := .dedicated) (readSome root all mine))
    for t in tasks do
      for lines in ← IO.ofExcept t.get do
        h.putStr lines
    h.flush
    done := done + part.size
    IO.eprintln s!"{done} of {mods.size} modules"
