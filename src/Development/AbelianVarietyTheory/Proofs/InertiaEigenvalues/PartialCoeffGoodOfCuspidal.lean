module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AugmentationLengthColengthBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldMirabolic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaSeriesUnfoldMirabolic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_coeff_good_of_cuspidal : ∀ (E : Type) [Field E] [NumberField E] (k m : ℕ) (hmk : m + 1 ≤ k) (φ : GA E (k + 1) → ℂ),
    Continuous φ → (∀ γ g, φ (ratGL E (k + 1) γ * g) = φ g) →
    (∀ r, 0 < r → r ≤ k → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (k + 1) r k)) (fun x => φ (blkU x * g)) = 0) →
    Good (GlobalTheory.StdCharConductor.psi E) m (fun h => partialCoeff φ (m + 1) (blockGL (by omega : m + 1 ≤ k + 1) h)) := by
  first | (exact @GlobalTheory.PartialBlock.good_partialCoeff_blockGL) | (exact GlobalTheory.PartialBlock.good_partialCoeff_blockGL) | (intros; apply GlobalTheory.PartialBlock.good_partialCoeff_blockGL  <;> assumption)
