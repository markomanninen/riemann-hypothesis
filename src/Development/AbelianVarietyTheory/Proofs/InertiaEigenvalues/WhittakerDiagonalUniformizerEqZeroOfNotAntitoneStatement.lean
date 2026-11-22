module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDiagonalUniformizerEqZeroOfNotAntitone
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRankinSelbergSchurTermFinsuppEulerProductStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_diagonalUniformizer_eq_zero_of_not_antitone : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (w : HeightOneSpectrum (𝓞 E)), w ∉ S →
    (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    ∀ (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), IsUnifV E w (ϖ w : w.adicCompletion E) →
    ∀ (W : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, W (g * finGL E (m + 1) κ) = W g) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ)), ¬ Antitone (l w) →
    ∀ p : GA E (m + 1), Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p = 1 →
    W (p * GlobalTheory.CellDec.tl (m + 1) ϖ l) = 0 := by
  first | exact @GlobalTheory.CellVanish.eq_zero_of_not_antitone | exact GlobalTheory.CellVanish.eq_zero_of_not_antitone | (intros; apply GlobalTheory.CellVanish.eq_zero_of_not_antitone <;> assumption)
