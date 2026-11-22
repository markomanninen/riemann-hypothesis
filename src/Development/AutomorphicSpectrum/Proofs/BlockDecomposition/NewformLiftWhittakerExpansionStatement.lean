module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftWhittakerExpansion
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_lift_whittaker_expansion : Ad3.R.F2 := by
  first | exact @GlobalTheory.CompanionTheory.RsWhittaker.whittaker_of_lift | exact GlobalTheory.CompanionTheory.RsWhittaker.whittaker_of_lift | (intros; apply GlobalTheory.CompanionTheory.RsWhittaker.whittaker_of_lift <;> assumption)
