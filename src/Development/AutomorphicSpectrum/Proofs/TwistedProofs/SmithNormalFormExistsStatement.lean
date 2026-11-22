module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.SmithNormalFormExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smith_normal_form_exists : Smith := by
  first | exact @GlobalTheory.CompanionTheory.InertSmith.smith | exact GlobalTheory.CompanionTheory.InertSmith.smith | (intros; apply GlobalTheory.CompanionTheory.InertSmith.smith <;> assumption)
