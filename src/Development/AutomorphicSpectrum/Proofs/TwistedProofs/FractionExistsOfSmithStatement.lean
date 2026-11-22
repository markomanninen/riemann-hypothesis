module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.FractionExistsOfSmith
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fraction_exists_of_smith : Smith → FracExists := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.fracExists_of_smith | exact GlobalTheory.CompanionTheory.InertZeta.fracExists_of_smith | (intros; apply GlobalTheory.CompanionTheory.InertZeta.fracExists_of_smith <;> assumption)
