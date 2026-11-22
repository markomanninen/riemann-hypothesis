module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupCommutantScalars
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

@[expose] public section

open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_commutant_scalars : GlobalTheory.RegSS.UnitaryCommutant := by
  first | exact @GlobalTheory.RegSS.unitaryCommutant | exact GlobalTheory.RegSS.unitaryCommutant | (intros; apply GlobalTheory.RegSS.unitaryCommutant <;> assumption)
