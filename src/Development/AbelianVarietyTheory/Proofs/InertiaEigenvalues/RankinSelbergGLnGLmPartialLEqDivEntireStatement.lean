module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergGLnGLmPartialLEqDivEntire
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankinSelberg_GLn_GLm_partialL_eq_div_entire : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n m : ℕ) (σ : CG E n) (σ' : CG E m), 1 ≤ m → m < n → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → UnrOutside T σ → UnrOutside T σ' → ∃ F H : ℂ → ℂ, Differentiable ℂ F ∧ Differentiable ℂ H ∧ (∀ x : ℝ, 0 < (H x).re ∧ (H x).im = 0) ∧ ∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (F x / H x) := by
  first | (exact @GlobalTheory.RSnmUnf.rs_nm_partialL_eq_div) | (exact GlobalTheory.RSnmUnf.rs_nm_partialL_eq_div) | (intros; apply GlobalTheory.RSnmUnf.rs_nm_partialL_eq_div  <;> assumption)
