module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianTraceFormOfTraceFormPerfect
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

@[expose] public section

open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTraceForm_of_traceForm_perfect : GlobalTheory.RegSS.TracePerfect → GlobalTheory.RegSS.TraceClause := by
  first | exact @GlobalTheory.RegSS.traceClause_of_tracePerfect | exact GlobalTheory.RegSS.traceClause_of_tracePerfect | (intros; apply GlobalTheory.RegSS.traceClause_of_tracePerfect <;> assumption)
