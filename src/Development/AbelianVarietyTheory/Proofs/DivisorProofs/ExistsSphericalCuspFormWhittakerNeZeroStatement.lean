module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSphericalCuspFormWhittakerNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spherical_cuspForm_whittaker_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → ∀ (π : CuspSub E (m + 1)) (α : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∃ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), act (.fin (locGL E (m + 1) w k)) φ = φ) ∧ ∃ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 x ≠ 0 := by
  first | exact @GlobalTheory.JSW.NzSph.exists_sph_whit_ne_zero | exact GlobalTheory.JSW.NzSph.exists_sph_whit_ne_zero | (intros; apply GlobalTheory.JSW.NzSph.exists_sph_whit_ne_zero <;> assumption)
