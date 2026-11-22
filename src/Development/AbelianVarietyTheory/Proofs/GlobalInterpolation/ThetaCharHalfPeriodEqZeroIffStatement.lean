module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaCharHalfPeriodEqZeroIff
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.EquidistributedConjugates
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PeriodLatticeAgreement
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JacobiThetaHalfCharacteristic
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DifferentiableAtDerivAtZero
public import Formalism.GL3MeanSquares.HookFormulaTorsion.FourFoldOrthogonalSum

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChar_half_period_eq_zero_iff_odd_add_odd_add : ∀ τ : UpperHalfPlane, ThetaConstantWeber.JacobiProduct τ → ∀ (m n : ℤ) (a b : Fin 2),
    JacobiThetaHalfCharacteristic.IsEvenChar a b →
    (JacobiThetaHalfCharacteristic.thetaChar a b (((m : ℂ) + (n : ℂ) * (τ : ℂ)) / 2) (τ : ℂ) = 0 ↔
      Odd (m + ((b : ℕ) : ℤ)) ∧ Odd (n + ((a : ℕ) : ℤ))) := by
  first | exact @GlobalTheory.Glob.ThetaParity.thetaChar_half_period_eq_zero_iff | exact GlobalTheory.Glob.ThetaParity.thetaChar_half_period_eq_zero_iff | (intros; apply GlobalTheory.Glob.ThetaParity.thetaChar_half_period_eq_zero_iff <;> assumption)
