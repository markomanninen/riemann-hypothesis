module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtalePolynomialModelOfDirectedUnion

@[expose] public section

open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_polynomial_descent_of_directed_union : ∀ (T : Type) [CommRing T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (𝒜 : ι → Subring T), Monotone 𝒜 → (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra.Etale (Polynomial T) E],
    ∃ (i : ι) (E₀ : Type) (_ : CommRing E₀) (_ : Algebra (Polynomial (𝒜 i)) E₀),
      Algebra.Etale (Polynomial (𝒜 i)) E₀ ∧
      (letI : Algebra (Polynomial (𝒜 i)) (Polynomial T) :=
        (Polynomial.mapRingHom (𝒜 i).subtype).toAlgebra
       Nonempty (TensorProduct (Polynomial (𝒜 i)) (Polynomial T) E₀ ≃ₐ[Polynomial T] E)) := by
  intro T _ ι _ _ _ 𝒜 hmono hcov E _ _ _
  let S : ι → Subring (Polynomial T) := fun i ↦ (Polynomial.mapRingHom (𝒜 i).subtype).range
  have hSmono : Monotone S := by
    intro i j hij p hp
    obtain ⟨q, rfl⟩ := RingHom.mem_range.mp hp
    refine RingHom.mem_range.mpr ⟨q.map (Subring.inclusion (hmono hij)), ?_⟩
    simp only [coe_mapRingHom, Polynomial.map_map]
    rfl
  have hScov : ∀ p, ∃ i, p ∈ S i := by
    classical
    intro p
    choose j hj using hcov
    obtain ⟨i, hi⟩ := Finset.exists_le (p.support.image (fun n ↦ j (p.coeff n)))
    refine ⟨i, ?_⟩
    have hp : p ∈ Polynomial.lifts (𝒜 i).subtype := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      by_cases hn : n ∈ p.support
      · exact ⟨⟨p.coeff n, hmono (hi _ (Finset.mem_image_of_mem _ hn)) (hj _)⟩, rfl⟩
      · rw [Polynomial.notMem_support_iff.mp hn]
        exact ⟨0, map_zero _⟩
    exact RingHom.mem_range.mpr hp
  obtain ⟨i, E₀, _, _, hE₀, ⟨φ⟩⟩ :=
    GlobalTheory.EtaleDescent.exists_etale_model_of_directed_union (Polynomial T) ι S hSmono hScov E
  let f : Polynomial (𝒜 i) →+* Polynomial T := Polynomial.mapRingHom (𝒜 i).subtype
  have hf : Function.Injective f := Polynomial.map_injective _ Subtype.val_injective
  let e : Polynomial (𝒜 i) ≃+* S i := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun a b h ↦ hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  let alg₀ : Algebra (Polynomial (𝒜 i)) E₀ := ((algebraMap (S i) E₀).comp e.toRingHom).toAlgebra
  let _ : Algebra (Polynomial (𝒜 i)) (Polynomial T) := f.toAlgebra
  have hEt : Algebra.Etale (Polynomial (𝒜 i)) E₀ := by
    rw [← RingHom.etale_algebraMap]
    exact RingHom.Etale.respectsIso.2 (algebraMap (S i) E₀) e
      (RingHom.etale_algebraMap.mpr hE₀)
  have hmapT (p : Polynomial (𝒜 i)) :
      algebraMap (S i) (Polynomial T) (e p) = algebraMap (Polynomial (𝒜 i)) (Polynomial T) p := rfl
  have hmapE (p : Polynomial (𝒜 i)) :
      algebraMap (S i) E₀ (e p) = algebraMap (Polynomial (𝒜 i)) E₀ p := rfl
  have : SMulCommClass (S i) (Polynomial (𝒜 i)) (Polynomial T) :=
    ⟨fun a b x ↦ by simp only [Algebra.smul_def]; ring⟩
  have : TensorProduct.CompatibleSMul (S i) (Polynomial (𝒜 i)) (Polynomial T) E₀ :=
    ⟨fun p m n ↦ by
      rw [Algebra.smul_def, Algebra.smul_def, ← hmapT, ← hmapE, ← Algebra.smul_def, ← Algebra.smul_def,
        TensorProduct.smul_tmul]⟩
  have : TensorProduct.CompatibleSMul (Polynomial (𝒜 i)) (S i) (Polynomial T) E₀ :=
    ⟨fun s m n ↦ by
      obtain ⟨p, rfl⟩ := e.surjective s
      rw [Algebra.smul_def, Algebra.smul_def, hmapT, hmapE, ← Algebra.smul_def, ← Algebra.smul_def,
        TensorProduct.smul_tmul]⟩
  refine ⟨i, E₀, inferInstance, alg₀, hEt, ⟨?_⟩⟩
  exact (Algebra.TensorProduct.equivOfCompatibleSMul (S i) (Polynomial (𝒜 i)) (Polynomial T)
    (Polynomial T) E₀).trans φ
