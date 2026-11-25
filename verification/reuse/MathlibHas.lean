/-
Ask Mathlib's own search and automation to prove statements of the compiled project.

Usage: PROBE_ROOT=... PROBE_LIST=... PROBE_OUT=... lake env lean MathlibHas.lean

Run it in a Lake project that requires the Mathlib revision of this repository and nothing
else. The environment of this file then holds Mathlib, its packages and Lean, and no constant
of the project. `mathlib_has.py` of this folder prepares the files and starts the runs.

PROBE_ROOT is a folder with the public compiled files `.olean` of the project's modules.
PROBE_LIST has one line for each statement, with three columns separated by tabs: the module,
the name of the theorem and the tactics to try, separated by commas. PROBE_OUT is the file that
the answers are added to.

A line whose name is `*` asks for theorems of the module that the script picks itself. It takes
the propositions of the module's file that are in the environment, are neither private nor
internal and were not made by Lean itself, as equation lemmas are. Of these it takes the
PROBE_FIRST ones whose names have the smallest hash, one by default.
`mathlib_has.py` uses this for its control, in which PROBE_ROOT holds the files of Mathlib.

For each line the script reads the compiled type of the theorem from the module's file, which
is its statement, and checks that every constant of the statement is in the environment. It
then makes a goal of that statement and runs each tactic on it within a limit of heartbeats.
It writes one line when a tactic starts and one when it ends. An end line has the columns
module, name, tactic, answer, milliseconds, the theorems that the proof found names, a text
and the limit of heartbeats, which PROBE_BEATS sets and which is 400,000 by default. The answer is `closed` when the tactic proved the statement, `failed` when it gave up,
`limit` when it ran out of heartbeats or of recursion depth, and `skipped` when the statement
could not be posed. Nothing of the project is imported, so a proof that is found uses the
libraries alone.
-/
import Mathlib
open Lean Meta Elab

namespace MathlibHas

def nameText (n : Name) : String := n.toString (escape := false)

/-- One line of text without tabs and line breaks, cut to a length. -/
def flat (s : String) (len : Nat := 300) : String :=
  String.ofList (((s.replace "\n" " ").replace "\t" " ").toList.take len)

/-- The tactics by the names that the list uses. -/
def tactics : CoreM (List (String × Syntax)) := do
  return [("exact?", ← `(tactic| (intros; exact?))),
          ("simp_all", ← `(tactic| (intros; simp_all))),
          ("aesop", ← `(tactic| aesop)),
          ("grind", ← `(tactic| grind))]

/-- Whether Lean made a theorem by itself, as it makes the equation lemmas of a definition and
the injectivity lemmas of a constructor. The test goes by the last part of the name. -/
def generated (n : Name) : Bool :=
  match n with
  | .str _ last => last ∈ ["inj", "injEq", "sizeOf_spec", "congr_simp", "eq_def", "eq_unfold"] ||
      (last.startsWith "eq_" && (last.toList.drop 3).all Char.isDigit)
  | _ => true

/-- The constants of one module's public compiled file. The memory that holds them stays in use
until the process ends. -/
unsafe def readTypes (root : System.FilePath) (m : String) : IO (Array ConstantInfo) := do
  let base := (m.splitOn ".").foldl (· / ·) root
  let parts ← readModuleDataParts #[base.addExtension "olean"]
  let some (data, _) := parts.back? | throw <| IO.userError s!"no compiled part of {m}"
  return data.constants

/-- Run one tactic on a fresh goal of the given type. Returns the answer, the theorems that the
proof names and a text, which is the suggestion of `exact?` or the error. -/
def attempt (type : Expr) (tac : Syntax) (beats : Nat) : MetaM (String × String × String) := do
  let saved ← saveState
  modifyThe Core.State fun s => { s with messages := {} }
  let answer ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := beats * 1000 }) <|
      withCurrHeartbeats do
        let goal ← mkFreshExprMVar type
        let rest ← Term.TermElabM.run' <| Tactic.run goal.mvarId! (Tactic.evalTactic tac)
        let proof ← instantiateMVars goal
        if !rest.isEmpty || proof.hasExprMVar then return ("failed", "", "goals remain")
        if proof.hasSorry then return ("failed", "", "the proof holds sorry")
        let env ← getEnv
        let thms := proof.getUsedConstants.filter fun n => (env.find? n).any (· matches .thmInfo _)
        let mut said := ""
        for msg in (← getThe Core.State).messages.toList do
          let text ← msg.data.toString
          if said == "" && (text.splitOn "Try this").length > 1 then said := text
        return ("closed", " ".intercalate ((thms.extract 0 12).map nameText).toList, said))
    (fun e => do
      let text ← e.toMessageData.toString
      return (if e.isRuntime then "limit" else "failed", "", text))
  saved.restore
  modifyThe Core.State fun s => { s with messages := {} }
  return answer

unsafe def run : MetaM Unit := do
  let some root ← IO.getEnv "PROBE_ROOT" | throwError "set PROBE_ROOT"
  let some list ← IO.getEnv "PROBE_LIST" | throwError "set PROBE_LIST"
  let some out ← IO.getEnv "PROBE_OUT" | throwError "set PROBE_OUT"
  let beats := ((← IO.getEnv "PROBE_BEATS").bind String.toNat?).getD 400000
  let first := ((← IO.getEnv "PROBE_FIRST").bind String.toNat?).getD 1
  let known ← tactics
  let h ← IO.FS.Handle.mk out .append
  let env ← getEnv
  for line in (← IO.FS.lines list) do
    let [m, asked, wanted] := line.splitOn "\t" | continue
    let all ← try readTypes root m catch e =>
      h.putStrLn s!"{m}\t{asked}\t*\tskipped\t0\t\t{flat (← e.toMessageData.toString)}"
      h.flush
      continue
    let mut chosen := #[]
    if asked == "*" then
      let mut fit := #[]
      for ci in all do
        if (ci matches .thmInfo _ || ci matches .axiomInfo _) && !ci.name.isInternal &&
            !isPrivateName ci.name && !generated ci.name && env.contains ci.name then
          if ← (isProp ci.type <|> pure false) then fit := fit.push ci
      chosen := (fit.qsort fun a b => hash a.name < hash b.name).extract 0 first
    else
      chosen := all.filter (nameText ·.name == asked)
    if chosen.isEmpty then
      h.putStrLn s!"{m}\t{asked}\t*\tskipped\t0\t\tthe module's file holds no such theorem"
      h.flush
    for ci in chosen do
      let name := nameText ci.name
      let absent := ci.type.getUsedConstants.filter fun n => !env.contains n
      let mut reason := ""
      if !absent.isEmpty then
        reason := "not in the environment: " ++ " ".intercalate ((absent.extract 0 6).map nameText).toList
      else
        try
          Meta.check ci.type
          unless ← isProp ci.type do reason := "the type is not a proposition"
        catch e => reason := "does not typecheck: " ++ (← e.toMessageData.toString)
      if reason != "" then
        h.putStrLn s!"{m}\t{name}\t*\tskipped\t0\t\t{flat reason}"
        h.flush
        continue
      for label in wanted.splitOn "," do
        let some (_, tac) := known.find? (·.1 == label) | continue
        h.putStrLn s!"{m}\t{name}\t{label}\tstart"
        h.flush
        let t0 ← IO.monoMsNow
        let (answer, thms, text) ← attempt ci.type tac beats
        h.putStrLn s!"{m}\t{name}\t{label}\t{answer}\t{(← IO.monoMsNow) - t0}\t{thms}\t{flat text}\t{beats}"
        h.flush

end MathlibHas

-- The command itself runs without a limit, and every tactic runs within its own.
set_option maxHeartbeats 0 in
#eval MathlibHas.run
