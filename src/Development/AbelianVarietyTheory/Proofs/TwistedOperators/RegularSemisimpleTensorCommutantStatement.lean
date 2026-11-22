module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleTensorCommutant
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

@[expose] public section

open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularSemisimple_tensor_commutant : GlobalTheory.RegSS.PointsCommutant := by
  first | exact @GlobalTheory.RegSS.pointsCommutant | exact GlobalTheory.RegSS.pointsCommutant | (intros; apply GlobalTheory.RegSS.pointsCommutant <;> assumption)
