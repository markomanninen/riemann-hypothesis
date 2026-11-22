module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanLogCovolumeConjugateLatticesEq
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ClassMeanPeriods
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.EquidistributedConjugates
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JacobiThetaHalfCharacteristic
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PeriodLatticeAgreement

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_log_covolume_conjugateLattices_eq : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)))) / (Module.finrank ℚ M : ℝ) = Real.log Real.pi + ClassMeanPeriods.classMeanValue D := by
  first | exact @GlobalTheory.MeanLogArea.mean_log_area | exact GlobalTheory.MeanLogArea.mean_log_area | (intros; apply GlobalTheory.MeanLogArea.mean_log_area <;> assumption)
