import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCSqsys
open Lean

def outside : List Name := [`Mathlib, `Batteries, `Init, `Lean, `Std, `Aesop, `Qq, `Plausible, `ProofWidgets,
  `ImportGraph, `LeanSearchClient, `Cli]

#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let own (n : Name) : Option Name := do
    let i ← env.getModuleIdxFor? n
    let m := mods[i.toNat]!
    if outside.contains m.getRoot then none else some m
  let h ← IO.FS.Handle.mk "deps.tsv" .write
  for (n, ci) in env.constants.toList do
    match own n with
    | none => pure ()
    | some m =>
      let used := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])
      let used := used.filter (fun c => (own c).isSome)
      let kind := match ci with
        | .thmInfo _ => "thm" | .defnInfo _ => "def" | .inductInfo _ => "ind" | .ctorInfo _ => "ctor"
        | .recInfo _ => "rec" | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"
      h.putStrLn s!"{m}\t{kind}\t{n}\t{" ".intercalate (used.toList.map toString)}"
