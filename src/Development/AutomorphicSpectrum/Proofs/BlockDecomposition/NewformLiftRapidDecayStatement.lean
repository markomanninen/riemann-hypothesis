module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftRapidDecay
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_lift_rapid_decay : Ad3.R.B0 → Ad3.R.F5 := by
  first | exact @GlobalTheory.CompanionTheory.NewformLiftDecay.main | exact GlobalTheory.CompanionTheory.NewformLiftDecay.main | (intros; apply GlobalTheory.CompanionTheory.NewformLiftDecay.main <;> assumption)
