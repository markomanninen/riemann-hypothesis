module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.VerticalDivisorsCommute
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_divisors_commute : GroundTheory.Heights₂.Heights.NumbersDVR.VerticalDivisorsCommute.Statement.{0} := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors.verticalDivisorsCommute | exact GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors.verticalDivisorsCommute | (intros; apply GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors.verticalDivisorsCommute <;> assumption)
