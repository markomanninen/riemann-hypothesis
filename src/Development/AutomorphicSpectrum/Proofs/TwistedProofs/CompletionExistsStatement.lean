module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.CompletionExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_exists : Completion := by
  first | exact @GlobalTheory.CompanionTheory.InertDoubling.completion | exact GlobalTheory.CompanionTheory.InertDoubling.completion | (intros; apply GlobalTheory.CompanionTheory.InertDoubling.completion <;> assumption)
