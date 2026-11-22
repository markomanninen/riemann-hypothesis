module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageTopOfVanishingBlockAver
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
theorem _root_.GlobalTheory.T.isMirabolicWhittakerStage_top_of_vanishing_blockAverages : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (ψ : AddChar (Ad E) ℂ) (f : GA E (m + 1) → ℂ),
    Continuous f → (∀ γ g, f (ratGL E (m + 1) γ * g) = f g) →
    (∀ r, 0 < r → r ≤ m → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (m + 1) r m)) (fun x => f (blkU x * g)) = 0) → Good ψ m f := by
  first | (exact @GlobalTheory.CuspGeneric.good_top) | (exact GlobalTheory.CuspGeneric.good_top) | (intros; apply GlobalTheory.CuspGeneric.good_top  <;> assumption)
