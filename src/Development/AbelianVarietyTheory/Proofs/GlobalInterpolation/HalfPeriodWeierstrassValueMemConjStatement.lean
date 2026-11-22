module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HalfPeriodWeierstrassValueMemConj
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
theorem _root_.GlobalTheory.T.halfPeriod_weierstrassValue_mem_conj : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t →
    ∃ e g : M, (g : ℂ) = g2 (lamOf D cc δ) ∧ lamConj M M.val (lamOf D cc δ) = lamOf D cc δ ∧
      ∀ ρ : M →ₐ[ℚ] ℂ, Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧
        g2 (lamConj M ρ (lamOf D cc δ)) = ρ g ∧ t ρ ∉ lamConj M ρ (lamOf D cc δ) ∧
        Formalism.MainNotions.StandardLatticesGL3.wpF (lamConj M ρ (lamOf D cc δ)) (t ρ) = ρ e := by
  first | exact @GlobalTheory.HalfPeriodValue.halfPeriod_value | exact GlobalTheory.HalfPeriodValue.halfPeriod_value | (intros; apply GlobalTheory.HalfPeriodValue.halfPeriod_value <;> assumption)
