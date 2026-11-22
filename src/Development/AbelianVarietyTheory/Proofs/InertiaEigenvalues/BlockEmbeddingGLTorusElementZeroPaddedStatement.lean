module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockEmbeddingGLTorusElementZeroPadded
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBumpShintani
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWhittakerBumpExtensionSchurComplementStatement

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockEmbeddingGL_torus_element_zero_padded : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ)
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ)),
    GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (GlobalTheory.JSW.tl ϖ l) =
      GlobalTheory.JSW.tl ϖ (l.mapRange GlobalTheory.RSnmUnf.padNat GlobalTheory.RSnmUnf.padNat_zero) := by
  first | (exact @GlobalTheory.JSW.blockGL_tl) | (exact GlobalTheory.JSW.blockGL_tl) | (intros; apply GlobalTheory.JSW.blockGL_tl  <;> assumption)
