module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.TameFrob

theorem exists_algEquiv_iotaO_sigma : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a], ∃ Φ : Om l ≃ₐ[ℚ_[l]] Om l,
    ∀ w : Wq l a, Φ (GlobalTheory.TameFrob.iotaO l a w) = GlobalTheory.TameFrob.iotaO l a (sigma l a w) := by
  intro l _ a _
  letI : Algebra (Wq l a) ↥(Kunr l a) := algK l a
  letI : IsFractionRing (Wq l a) ↥(Kunr l a) := by
    refine (isLocalization_iff (nonZeroDivisors (Wq l a)) ↥(Kunr l a)).2 ⟨?_, ?_, ?_⟩
    · intro s
      refine IsUnit.mk0 _ fun h => nonZeroDivisors.coe_ne_zero s (iota_injective l a ?_)
      rw [← algebraMap_K, h, map_zero]
    · intro y
      obtain ⟨w, s, hs, h⟩ := exists_frac l a y
      exact ⟨⟨w, ⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩⟩, Subtype.ext (by simpa [algebraMap_K] using h)⟩
    · intro x y h
      exact ⟨1, by rw [iota_injective l a h]⟩
  let fr : ↥(Kunr l a) →+* Om l :=
    IsFractionRing.lift (g := (iotaO l a).comp (sigma l a).toRingEquiv.toRingHom)
      ((iotaO_injective l a).comp (sigma l a).injective)
  have hfr (w : Wq l a) : fr (iota l a w) = iotaO l a (sigma l a w) :=
    IsFractionRing.lift_algebraMap _ w
  let f : ↥(Kunr l a) →ₐ[ℚ_[l]] Om l := {
    toRingHom := fr
    commutes' := by
      intro r
      have h : fr.comp (algebraMap ℚ_[l] ↥(Kunr l a)) = algebraMap ℚ_[l] (Om l) := by
        refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (RingHom.ext fun u => ?_)
        have h1 : algebraMap ℚ_[l] ↥(Kunr l a) (algebraMap ℤ_[l] ℚ_[l] u) =
            iota l a (algebraMap ℤ_[l] (Wq l a) u) :=
          Subtype.ext (by rw [coe_iota, iotaO_algebraMap]; rfl)
        simp only [RingHom.comp_apply]
        rw [h1, hfr, AlgEquiv.commutes, iotaO_algebraMap]
        rfl
      exact RingHom.congr_fun h r }
  let φ : Om l →ₐ[ℚ_[l]] Om l := f.liftNormal (Om l)
  refine ⟨AlgEquiv.ofBijective φ φ.normal_bijective, fun w => ?_⟩
  have h := AlgHom.liftNormal_commutes f (Om l) (iota l a w)
  rw [AlgEquiv.ofBijective_apply]
  exact h.trans (hfr w)

end GlobalTheory.TameFrob
