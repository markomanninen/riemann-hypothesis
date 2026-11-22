module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem isCM_of_conj (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (h : ∀ x : K, ∃ y : K, ∀ φ : K →+* ℂ, φ y = starRingEnd ℂ (φ x)) : IsCMField K := by
  classical
  choose c hc using h
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  have hcc : ∀ x, c (c x) = x := fun x => φ.injective (by rw [hc, hc, Complex.conj_conj])
  let τ : K ≃+* K :=
    { toFun := c
      invFun := c
      left_inv := hcc
      right_inv := hcc
      map_mul' := fun x y => φ.injective (by simp only [hc, map_mul])
      map_add' := fun x y => φ.injective (by simp only [hc, map_add (f := _)]) }
  let σ : K ≃ₐ[ℚ] K := AlgEquiv.ofRingEquiv (f := τ) (fun q => by simp)
  have hσ : ∀ ψ : K →+* ℂ, ComplexEmbedding.IsConj ψ σ := fun ψ => by
    ext x
    exact (hc x ψ).symm
  have hσ' : Nat.card (Subgroup.zpowers σ) = 2 := by
    rw [Nat.card_zpowers, ComplexEmbedding.orderOf_isConj_two_of_ne_one (hσ φ)]
    exact (ComplexEmbedding.isConj_ne_one_iff (hσ φ)).mpr <| IsTotallyComplex.complexEmbedding_not_isReal φ
  let L := (FixedPoints.intermediateField (Subgroup.zpowers σ) : IntermediateField ℚ K)
  have : IsTotallyReal L := ⟨fun w ↦ by
    obtain ⟨W, rfl⟩ := w.comap_surjective (K := K)
    dsimp only
    rw [← InfinitePlace.mk_embedding W, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff,
      ComplexEmbedding.isReal_iff]
    ext x
    have hx : c x.1 = x.1 := x.2 ⟨σ, Subgroup.mem_zpowers σ⟩
    have := hc x.1 W.embedding
    rw [hx] at this
    exact this.symm⟩
  have : Algebra.IsQuadraticExtension L K := ⟨by
    have : Fintype (Subgroup.zpowers σ) := Fintype.ofFinite _
    rw [← hσ', Nat.card_eq_fintype_card]
    exact FixedPoints.finrank_eq_card (Subgroup.zpowers σ) K⟩
  exact IsCMField.ofCMExtension L K
