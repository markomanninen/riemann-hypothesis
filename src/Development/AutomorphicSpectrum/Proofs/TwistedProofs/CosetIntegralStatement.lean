module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.CosetIntegral
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetIntegral' : CosetIntegral := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.cosetIntegral | exact GlobalTheory.CompanionTheory.InertZeta.cosetIntegral | (intros; apply GlobalTheory.CompanionTheory.InertZeta.cosetIntegral <;> assumption)
