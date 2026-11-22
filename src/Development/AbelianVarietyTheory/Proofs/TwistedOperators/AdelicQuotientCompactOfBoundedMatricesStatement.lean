module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicQuotientCompactOfBoundedMatrices
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

@[expose] public section

open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_quotient_compact_of_bounded_matrices : GlobalTheory.RegSS.TensorLattice → GlobalTheory.RegSS.CompactOfMatBounded := by
  first | exact @GlobalTheory.RegSS.CptQuot.compactOfMatBounded | exact GlobalTheory.RegSS.CptQuot.compactOfMatBounded | (intros; apply GlobalTheory.RegSS.CptQuot.compactOfMatBounded <;> assumption)
