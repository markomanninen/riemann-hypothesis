module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ComplexMultiplicationJacquetShalika
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_multiplication_jacquet_shalika : GlobalTheory.Published.ComplexMultiplicationJSt := by
  first | exact @GlobalTheory.CompanionTheory.Published.complexMultiplicationJ | exact GlobalTheory.CompanionTheory.Published.complexMultiplicationJ | (intros; apply GlobalTheory.CompanionTheory.Published.complexMultiplicationJ <;> assumption)
