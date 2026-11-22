module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentraliserPointsBoundedOfNormOneBounded
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

@[expose] public section

open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centraliser_points_bounded_of_normOne_bounded : GlobalTheory.RegSS.MatOfNormBounded := by
  first | exact @GlobalTheory.RegSS.MatBd.matOfNormBounded | exact GlobalTheory.RegSS.MatBd.matOfNormBounded | (intros; apply GlobalTheory.RegSS.MatBd.matOfNormBounded <;> assumption)
