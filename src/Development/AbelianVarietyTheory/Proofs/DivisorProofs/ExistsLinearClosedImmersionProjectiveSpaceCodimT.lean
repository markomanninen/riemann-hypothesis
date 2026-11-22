module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.LinearCodimTwo

open GlobalTheory.ProjSpace GlobalTheory.Adelic

theorem exists_linear_closedImmersion_two_le_ringKrullDim_stalk :
    ∀ (F : Type) [Field F] (N : ℕ), ∃ ℓ : PSpace F N ⟶ PSpace F (N + 2), IsClosedImmersion ℓ ∧
      ℓ ≫ PSpace.str F (N + 2) = PSpace.str F N ∧
      ∀ y, 2 ≤ ringKrullDim ((PSpace F (N + 2)).presheaf.stalk (ℓ y)) := by
  intro F _ N
  have h1 : Function.Injective (Fin.castSucc : Fin (N + 1) → Fin (N + 1 + 1)) := Fin.castSucc_injective _
  have h2 : Function.Injective (Fin.castSucc : Fin (N + 1 + 1) → Fin (N + 2 + 1)) := Fin.castSucc_injective _
  let ℓ₁ : PSpace F N ⟶ PSpace F (N + 1) := linearι F h1
  let ℓ₂ : PSpace F (N + 1) ⟶ PSpace F (N + 2) := linearι F h2
  have linear_str (A B : ℕ) {e : Fin (A + 1) → Fin (B + 1)}
      (he : Function.Injective e) : linearι F he ≫ PSpace.str F B = PSpace.str F A := by
    refine (Proj.mapAffineOpenCover (killHom F he)
      (irrelevant_le_map_of_surjective _ (killHom_surjective F he))).openCover.hom_ext _ _ fun s => ?_
    have key : ∀ (d : ℕ) (hd : 0 < d) (s : MvPolynomial (Fin (B + 1)) F) (hs : s ∈ grading F B d),
        Proj.awayι (grading F A) (killHom F he s) ((killHom F he).2 hs) hd ≫ linearι F he ≫ PSpace.str F B =
          Proj.awayι (grading F A) (killHom F he s) ((killHom F he).2 hs) hd ≫ PSpace.str F A := by
      intro d hd s hs
      rw [linearι, Proj.awayι_comp_map_assoc _ _ hd s hs, PSpace.str, PSpace.str, Proj.awayι_toSpecZero_assoc,
        Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext1
      refine RingHom.ext fun r => HomogeneousLocalization.val_injective _ ?_
      refine (congrArg HomogeneousLocalization.val (HomogeneousLocalization.Away.map_mk (killHom F he) s hs 0 (MvPolynomial.C r)
        ((zero_smul ℕ d).symm ▸ MvPolynomial.isHomogeneous_C _ r))).trans ?_
      rw [HomogeneousLocalization.Away.val_mk]
      exact congrArg (Localization.mk · _) (MvPolynomial.killCompl_C he r)
    exact key _ s.1.2 _ s.2.2
  refine ⟨ℓ₁ ≫ ℓ₂, inferInstance, by rw [Category.assoc, linear_str _ _ h2, linear_str _ _ h1], fun y => ?_⟩
  have last1 : Fin.last (N + 1) ∉ Set.range (Fin.castSucc : Fin (N + 1) → Fin (N + 1 + 1)) := by
    rintro ⟨i, hi⟩; exact Fin.castSucc_ne_last i hi
  have last2 : Fin.last (N + 2) ∉ Set.range (Fin.castSucc : Fin (N + 1 + 1) → Fin (N + 2 + 1)) := by
    rintro ⟨i, hi⟩; exact Fin.castSucc_ne_last i hi
  have n1 : ℓ₁ y ∉ chart F (N + 1) (Fin.last (N + 1)) := fun h => by
    have : y ∈ ℓ₁ ⁻¹ᵁ chart F (N + 1) (Fin.last (N + 1)) := h
    rw [linearι_preimage_chart_of_notMem F h1 last1] at this
    exact this
  have n2 (z : PSpace F (N + 1)) : ℓ₂ z ∉ chart F (N + 2) (Fin.last (N + 2)) := fun h => by
    have : z ∈ ℓ₂ ⁻¹ᵁ chart F (N + 2) (Fin.last (N + 2)) := h
    rw [linearι_preimage_chart_of_notMem F h2 last2] at this
    exact this
  have s1 : projSys.gen F (N + 1) ⤳ ℓ₁ y :=
    specializes_iff_mem_closure.2 ((ProjectiveSpectrum.le_iff_mem_closure _ _ _).1
      (show ⊥ ≤ (ℓ₁ y).asHomogeneousIdeal from bot_le))
  have s2 : projSys.gen F (N + 2) ⤳ ℓ₂ (projSys.gen F (N + 1)) :=
    specializes_iff_mem_closure.2 ((ProjectiveSpectrum.le_iff_mem_closure _ _ _).1
      (show ⊥ ≤ (ℓ₂ (projSys.gen F (N + 1))).asHomogeneousIdeal from bot_le))
  have lt1 : ℓ₂ (ℓ₁ y) < ℓ₂ (projSys.gen F (N + 1)) := by
    refine lt_of_le_not_ge ((Scheme.le_iff_specializes).2 (s1.map ℓ₂.continuous)) fun h => ?_
    have := ℓ₂.isClosedEmbedding.injective ((Scheme.le_iff_specializes.1 h).antisymm (s1.map ℓ₂.continuous)).eq
    exact n1 (this ▸ projSys.gen_mem F (N + 1) (Fin.last (N + 1)))
  have lt2 : ℓ₂ (projSys.gen F (N + 1)) < projSys.gen F (N + 2) := by
    refine lt_of_le_not_ge ((Scheme.le_iff_specializes).2 s2) fun h => ?_
    have e : ℓ₂ (projSys.gen F (N + 1)) = projSys.gen F (N + 2) := ((Scheme.le_iff_specializes.1 h).antisymm s2).eq
    exact n2 _ (by rw [e]; exact projSys.gen_mem F (N + 2) (Fin.last (N + 2)))
  have hc : (2 : ℕ∞) ≤ Order.coheight (ℓ₂ (ℓ₁ y)) := by
    have a := Order.coheight_add_one_le lt1
    have b := Order.coheight_add_one_le lt2
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ Order.coheight (projSys.gen F (N + 2)) + 1 + 1 := by gcongr; exact zero_le
      _ ≤ Order.coheight (ℓ₂ (projSys.gen F (N + 1))) + 1 := by gcongr
      _ ≤ _ := a
  rw [Scheme.Hom.comp_apply, ringKrullDim_stalk_eq_coheight]
  have := WithBot.coe_le_coe.2 hc
  simpa using this

end GlobalTheory.LinearCodimTwo
