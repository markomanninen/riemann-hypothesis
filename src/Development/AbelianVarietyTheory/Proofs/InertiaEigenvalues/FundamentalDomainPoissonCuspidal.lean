module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntersectionFamilyMultilinear
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
theorem _root_.GlobalTheory.T.fundamental_domain_poisson_cuspidal : ∀ (E : Type) [Field E] [NumberField E] (k m : ℕ) (hmk : m + 1 ≤ k) (φ : GA E (k + 1) → ℂ),
    Continuous φ → (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) → (∀ γ g, φ (ratGL E (k + 1) γ * g) = φ g) →
    (∀ r, 0 < r → r ≤ k → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (k + 1) r k)) (fun x => φ (blkU x * g)) = 0) →
    ∀ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)),
    ∀ γ : {ξ : Fin (m + 1) → E // ξ ≠ 0} → GL (Fin (m + 1)) E,
    (∀ ξ, Matrix.vecMul (Pi.single (Fin.last m) 1 : Fin (m + 1) → E) (γ ξ).val = ξ.1) → ∀ h : GA E (m + 1),
    HasSum (fun ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0} =>
        GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (Matrix.vecMul (algebraMap E (Ad E) ∘ ξ.1) h.val) *
          partialCoeff φ (m + 1) (blockGL (by omega : m + 1 ≤ k + 1) (ratGL E (m + 1) (γ ξ) * h)))
      (partialCoeff (GlobalTheory.RSnm.colSmooth (m + 1) F φ) (m + 1 + 1) (blockGL (by omega : m + 1 ≤ k + 1) h)) := by
  first | (exact @GlobalTheory.ColFourier.hasSum_colSmooth) | (exact GlobalTheory.ColFourier.hasSum_colSmooth) | (intros; apply GlobalTheory.ColFourier.hasSum_colSmooth  <;> assumption)
