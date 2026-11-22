module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevelCharacter
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_lift_level_character : Ad3.R.B0 → Ad3.R.AutomorphicLevelEquivariance := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel.lift_local_invariance | exact GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel.lift_local_invariance | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel.lift_local_invariance <;> assumption)
