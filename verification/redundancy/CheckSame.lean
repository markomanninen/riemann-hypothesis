/-
Compare the compiled statements of declarations that the text scan takes as the same.

Usage: lake env lean --run verification/redundancy/CheckSame.lean MODE ROOT GROUPS OUT

GROUPS has one row per declaration, with a group name, a module and a declaration name,
separated by tabs. A group whose name starts with D holds definitions, and any other group
holds theorems. OUT gets the same rows with three more columns: whether the constant was
found, its kind, and a number that members of the group with the same statement share.

In the mode `terms` the script reads the public compiled file of each module under ROOT, for
example `.lake/build/lib/lean`, and compares the terms as they are. In the mode `unfold` it
loads the modules with everything they import and lets Lean unfold definitions, which takes
far longer. ROOT is not used in that mode.

A theorem's statement is its type. A definition is compared by its type and its value together.

Only the public part of each compiled module is read. A declaration marked `private` is
therefore not found, and a definition whose value the module does not expose is compared by
its type alone.
-/
import Lean
open Lean Meta

def outside : List Name := [`Mathlib, `Batteries, `Init, `Lean, `Std, `Aesop, `Qq, `Plausible,
  `ProofWidgets, `ImportGraph, `LeanSearchClient, `Cli]

/-- The universe parameters are renamed by position, so that two copies with other parameter
names compare as equal. -/
def byPosition (ci : ConstantInfo) (e : Expr) : Expr :=
  e.instantiateLevelParams ci.levelParams
    ((List.range ci.levelParams.length).map fun i => Level.param (Name.mkNum `u i))

def kindOf : ConstantInfo → String
  | .thmInfo _ => "thm" | .defnInfo _ => "def" | .inductInfo _ => "ind" | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec" | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"

/-- The terms that make up the statement of a declaration. -/
def statement (isDef : Bool) (ci : ConstantInfo) : List Expr :=
  if !isDef then [byPosition ci ci.type]
  else match ci.value? (allowOpaque := true) with
    | some v => [byPosition ci ci.type, byPosition ci v]
    | none => [byPosition ci ci.type]

def sameTerms (isDef : Bool) (a b : ConstantInfo) : Bool :=
  statement isDef a == statement isDef b

def sameByUnfolding (isDef : Bool) (a b : ConstantInfo) : MetaM Bool := do
  let sa := statement isDef a
  let sb := statement isDef b
  if sa.length != sb.length then return false
  for (x, y) in sa.zip sb do
    unless ← withNewMCtxDepth (isDefEq x y) do return false
  return true

/-- Number the members of a group so that members with the same statement share a number. -/
def cluster (cis : Array (Option ConstantInfo)) (same : ConstantInfo → ConstantInfo → IO Bool) :
    IO (Array Int) := do
  let mut reps : Array ConstantInfo := #[]
  let mut out : Array Int := #[]
  for c? in cis do
    match c? with
    | none => out := out.push (-1)
    | some c =>
      let mut found : Option Nat := none
      for h : i in [0:reps.size] do
        if found.isNone then
          if ← same reps[i] c then found := some i
      match found with
      | some i => out := out.push i
      | none => out := out.push reps.size; reps := reps.push c
  return out

def userKey (n : Name) : String := (privateToUserName n).toString (escape := false)

/-- The wanted constants of some modules, read from the public compiled file of each. The
constants live in the memory regions that are returned with them. -/
unsafe def readSome (root : System.FilePath) (work : Array (String × Array String)) :
    IO (Array ((String × String) × ConstantInfo) × Array CompactedRegion) := do
  let mut out := #[]
  let mut regions := #[]
  for (m, wanted) in work do
    let path := (m.splitOn ".").foldl (· / ·) root |>.addExtension "olean"
    let (data, region) ← readModuleData path
    regions := regions.push region
    for h : i in [0:data.constNames.size] do
      let key := userKey data.constNames[i]
      if wanted.contains key then
        if let some ci := data.constants[i]? then out := out.push ((m, key), ci)
  return (out, regions)

unsafe def loadTerms (root : System.FilePath) (rows : Array (String × String × String)) :
    IO (Std.HashMap (String × String) ConstantInfo × Array CompactedRegion) := do
  let mut wanted : Std.HashMap String (Array String) := {}
  for (_, m, n) in rows do
    wanted := wanted.insert m ((wanted.getD m #[]).push n)
  let work := wanted.toArray
  let workers := 4
  let mut tasks := #[]
  for w in [0:workers] do
    let part := (Array.range work.size).filterMap fun i => if i % workers == w then work[i]? else none
    tasks := tasks.push (← IO.asTask (prio := .dedicated) (readSome root part))
  let mut found : Std.HashMap (String × String) ConstantInfo := {}
  let mut regions := #[]
  for t in tasks do
    let (part, rs) ← IO.ofExcept t.get
    regions := regions ++ rs
    for (k, ci) in part do
      found := found.insert k ci
  return (found, regions)

unsafe def loadAll (rows : Array (String × String × String)) :
    IO (Environment × Std.HashMap (String × String) ConstantInfo) := do
  initSearchPath (← findSysroot)
  let mut seen : Std.HashSet String := {}
  for (_, m, _) in rows do seen := seen.insert m
  let env ← importModules (seen.toArray.map fun m => { module := m.toName }) {} (trustLevel := 1024)
    (loadExts := false) (level := .exported)
  IO.eprintln s!"loaded {env.header.moduleNames.size} modules"
  let mods := env.header.moduleNames
  let found : Std.HashMap (String × String) ConstantInfo :=
    env.constants.fold (init := {}) fun acc n ci =>
      if n.isInternalDetail then acc else
      match env.getModuleIdxFor? n with
      | none => acc
      | some i =>
        let m := mods[i.toNat]!
        if outside.contains m.getRoot then acc else acc.insert (m.toString, userKey n) ci
  return (env, found)

/-- Compare the members of each group among the rows and write one line per row. -/
def writeGroups (h : IO.FS.Handle) (rows : Array (String × String × String))
    (found : Std.HashMap (String × String) ConstantInfo)
    (same : Bool → ConstantInfo → ConstantInfo → IO Bool) : IO Unit := do
  let flush (group : Array (String × String × String)) : IO Unit := do
    if group.isEmpty then return
    let isDef := group[0]!.1.startsWith "D"
    let cis := group.map fun (_, m, n) => found.get? (m, n)
    let numbers ← cluster cis (same isDef)
    for h' : i in [0:group.size] do
      let (g, m, n) := group[i]
      let hit := if cis[i]!.isSome then "1" else "0"
      let kind := (cis[i]!.map kindOf).getD ""
      h.putStrLn s!"{g}\t{m}\t{n}\t{hit}\t{kind}\t{numbers[i]!}"
  let mut current := ""
  let mut group : Array (String × String × String) := #[]
  for row in rows do
    if row.1 != current then
      flush group
      group := #[]
      current := row.1
    group := group.push row
  flush group
  h.flush

unsafe def main (args : List String) : IO Unit := do
  let [mode, root, groupsPath, outPath] := args
    | throw <| IO.userError "usage: CheckSame.lean (terms|unfold) ROOT GROUPS OUT"
  let mut rows : Array (String × String × String) := #[]
  for line in ← IO.FS.lines groupsPath do
    if let [g, m, n] := line.splitOn "\t" then rows := rows.push (g, m, n)
  let h ← IO.FS.Handle.mk outPath .write
  if mode == "unfold" then
    let (env, found) ← loadAll rows
    let ctx : Core.Context := { fileName := "<check>", fileMap := default, maxHeartbeats := 20000000 }
    writeGroups h rows found fun isDef a b => do
      if sameTerms isDef a b then return true
      try
        let (r, _) ← (sameByUnfolding isDef a b).run'.toIO ctx { env }
        return r
      catch _ => return false
  else
    -- The rows are handled a few thousand modules at a time, and the memory of each batch is
    -- released before the next one, so that the number of open compiled files stays small.
    let mut batch : Array (String × String × String) := #[]
    let mut modules : Std.HashSet String := {}
    let mut done := 0
    let run (batch : Array (String × String × String)) : IO Unit := do
      let (found, regions) ← loadTerms root batch
      writeGroups h batch found fun isDef a b => pure (sameTerms isDef a b)
      for r in regions do r.free
    for i in [0:rows.size] do
      let row := rows[i]!
      if modules.size ≥ 3000 && (batch.back?.map (·.1)) != some row.1 then
        run batch
        done := done + batch.size
        IO.eprintln s!"{done} of {rows.size} rows"
        batch := #[]
        modules := {}
      batch := batch.push row
      modules := modules.insert row.2.1
    run batch
