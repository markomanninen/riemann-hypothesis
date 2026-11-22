module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateFactorPointsSeparate
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

@[expose] public section

open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_factor_points_separate : GlobalTheory.RegSS.SeparatingPoints := by
  first | exact @GlobalTheory.RegSS.separatingPoints | exact GlobalTheory.RegSS.separatingPoints | (intros; apply GlobalTheory.RegSS.separatingPoints <;> assumption)
