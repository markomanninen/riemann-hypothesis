module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FieldAdelicUnitTranslateBoundedOfSmallMultiples
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

@[expose] public section

open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fieldAdelicUnitTranslateBounded_of_smallMultiples : GlobalTheory.RegSS.NormOnePacking → GlobalTheory.RegSS.TensorLattice → GlobalTheory.RegSS.FieldUnitBounded := by
  first | exact @GlobalTheory.RegSS.fieldUnitBounded_of_packing | exact GlobalTheory.RegSS.fieldUnitBounded_of_packing | (intros; apply GlobalTheory.RegSS.fieldUnitBounded_of_packing <;> assumption)
