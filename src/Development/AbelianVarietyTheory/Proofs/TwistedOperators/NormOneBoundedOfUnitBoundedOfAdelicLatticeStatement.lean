module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormOneBoundedOfUnitBoundedOfAdelicLattice
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

@[expose] public section

open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normOfUnitBounded_of_tensorLattice' : GlobalTheory.RegSS.TensorLattice → GlobalTheory.RegSS.NormOfUnitBounded := by
  first | exact @GlobalTheory.RegSS.normOfUnitBounded_of_tensorLattice | exact GlobalTheory.RegSS.normOfUnitBounded_of_tensorLattice | (intros; apply GlobalTheory.RegSS.normOfUnitBounded_of_tensorLattice <;> assumption)
