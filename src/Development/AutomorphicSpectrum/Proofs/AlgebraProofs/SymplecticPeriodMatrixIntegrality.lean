module

public import Mathlib
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MulEqSmulOneSymm

@[expose] public section

open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem gp_mat_lattice :
    ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
      v.Integers R → ∀ (g : ℕ) (Ht Bt : Matrix (Fin g) (Fin g ⊕ Fin g) R)
        (E : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R) (cp : R),
        cp ≠ 0 → Eᵀ = -E → IsUnit E.det → Btᵀ * Ht - Htᵀ * Bt = cp • E →
          let φ := algebraMap R C
          let intg : (Fin g → C) → Prop := fun w => ∀ k, v (w k) ≤ 1
          let hb : Matrix (Fin g ⊕ Fin g) (Fin g) C := ((Eᵀ)⁻¹ * Htᵀ).map φ
          v (φ (Matrix.fromRows Ht Bt).det) = v (φ cp) ^ g ∧
            (∀ x : Fin g ⊕ Fin g → C, ((Ht.map φ) *ᵥ x = 0 ∧ intg ((Bt.map φ) *ᵥ x)) ↔
              ∃ w, intg w ∧ x = (φ cp)⁻¹ • (hb *ᵥ w)) ∧
            (∀ w, intg w → ∃ x : Fin g ⊕ Fin g → C,
              (Ht.map φ) *ᵥ x = w ∧ (Bt.map φ) *ᵥ x = 0) ∧
            (∀ l : Fin g ⊕ Fin g → R,
              cp • l ∈ Submodule.span R (Set.range fun k => Matrix.fromRows Ht Bt k)) := by
  intro C _ v R _ _ hv g Ht Bt E cp hcp hE hEu hform φ intg hb
  have : IsDomain R := hv.hom_inj.isDomain _
  have hcp' : φ cp ≠ 0 := fun h => hcp (hv.hom_inj (by rw [map_zero]; exact h))
  have hEt : IsUnit (Eᵀ).det := by rwa [det_transpose]
  set U : Matrix (Fin g ⊕ Fin g) (Fin g) R := -((Eᵀ)⁻¹ * Btᵀ) with hU
  set W : Matrix (Fin g ⊕ Fin g) (Fin g) R := (Eᵀ)⁻¹ * Htᵀ with hW
  have h1 : U * Ht + W * Bt = cp • (1 : Matrix _ _ R) := by
    have : U * Ht + W * Bt = (Eᵀ)⁻¹ * (-(Btᵀ * Ht - Htᵀ * Bt)) := by
      rw [hU, hW, neg_sub, Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc]
      abel
    rw [this, hform, ← smul_neg, ← hE, Matrix.mul_smul, nonsing_inv_mul _ hEt]
  have h2 : fromCols U W * fromRows Ht Bt = cp • (1 : Matrix _ _ R) := by
    rw [fromCols_mul_fromRows, h1]
  have h3 := PositivityTheory.HtPt.Rh.mul_eq_smul_one_symm hcp h2
  rw [fromRows_mul_fromCols, ← fromBlocks_one, fromBlocks_smul, fromBlocks_inj] at h3
  obtain ⟨a11, a12, a21, a22⟩ := h3
  rw [smul_zero] at a12 a21
  have hone : ∀ {n : Type} [DecidableEq n], (cp • (1 : Matrix n n R)).map φ = φ cp • (1 : Matrix n n C) := by
    intro n _
    ext i j
    by_cases h : i = j <;> simp [h]
  have b1 := congrArg (·.map φ) h1
  have b11 := congrArg (·.map φ) a11
  have b12 := congrArg (·.map φ) a12
  have b21 := congrArg (·.map φ) a21
  have b22 := congrArg (·.map φ) a22
  simp only [Matrix.map_add _ (map_add φ), Matrix.map_mul, hone, Matrix.map_zero _ (map_zero φ)]
    at b1 b11 b12 b21 b22
  refine ⟨?_, fun x => ⟨fun hx => ⟨_, hx.2, ?_⟩, ?_⟩, fun w _ => ⟨(φ cp)⁻¹ • (U.map φ *ᵥ w), ?_, ?_⟩,
    fun l => ?_⟩
  · have hJ : (fromRows Ht Bt)ᵀ * Matrix.J (Fin g) R * fromRows Ht Bt = cp • E := by
      rw [← hform, Matrix.J, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
      simp [sub_eq_add_neg]
    have hd := congrArg (fun M => v (φ M.det)) hJ
    simp only [det_mul, det_transpose, det_smul, map_mul, map_pow, Fintype.card_sum,
      Fintype.card_fin] at hd
    rw [hv.one_of_isUnit (Matrix.isUnit_det_J (Fin g) R), hv.one_of_isUnit hEu, mul_one, mul_one,
      pow_add] at hd
    exact (mul_self_inj zero_le zero_le).1 hd
  · have := congrArg (· *ᵥ x) b1
    simp only [add_mulVec, ← mulVec_mulVec, hx.1, mulVec_zero, zero_add, smul_mulVec,
      one_mulVec] at this
    change x = (φ cp)⁻¹ • (W.map φ *ᵥ _)
    rw [this, inv_smul_smul₀ hcp']
  · rintro ⟨w, hw, rfl⟩
    change Ht.map φ *ᵥ ((φ cp)⁻¹ • (W.map φ *ᵥ w)) = 0 ∧
      intg (Bt.map φ *ᵥ ((φ cp)⁻¹ • (W.map φ *ᵥ w)))
    rw [mulVec_smul, mulVec_smul, mulVec_mulVec, mulVec_mulVec, b12, b22, zero_mulVec, smul_zero,
      smul_mulVec, one_mulVec, inv_smul_smul₀ hcp']
    exact ⟨rfl, hw⟩
  · rw [mulVec_smul, mulVec_mulVec, b11, smul_mulVec, one_mulVec, inv_smul_smul₀ hcp']
  · rw [mulVec_smul, mulVec_mulVec, b21, zero_mulVec, smul_zero]
  · have : cp • l = (l ᵥ* fromCols U W) ᵥ* fromRows Ht Bt := by
      rw [vecMul_vecMul, h2, vecMul_smul, vecMul_one]
    rw [this, vecMul_eq_sum]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.GR
