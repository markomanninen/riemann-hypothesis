module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel

@[expose] public section

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW

theorem unip_mem_symplecticGroup {ι : Type} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℚ}
    (hX : X.IsSymm) : (fromBlocks 1 X 0 1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) ∈ symplecticGroup ι ℚ := by
  simp [SymplecticGroup.fromBlocks_mem_iff, hX.eq]

theorem symplectic_eq_parabolic_J_parabolic_J_parabolic :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → ∃ p₁ ∈ Matrix.symplecticGroup ι ℚ, ∃ p₂ ∈ Matrix.symplecticGroup ι ℚ, ∃ p₃ ∈ Matrix.symplecticGroup ι ℚ, p₁.toBlocks₂₁ = 0 ∧ p₂.toBlocks₂₁ = 0 ∧ p₃.toBlocks₂₁ = 0 ∧ σ = p₁ * Matrix.J ι ℚ * p₂ * Matrix.J ι ℚ * p₃ := by
  intro ι _ _ σ hσ
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, σ = fromBlocks A B C D :=
    ⟨_, _, _, _, σ.fromBlocks_toBlocks.symm⟩
  have hb := (SymplecticGroup.fromBlocks_mem_iff.1 hσ).1
  have hex : ∃ X : Matrix ι ι ℚ, X.IsSymm ∧ IsUnit (A + X * C).det := by
    have hker (x : ι → ℚ) (hAx : A *ᵥ x = 0) (hCx : C *ᵥ x = 0) : x = 0 := by
      have h :
          fromBlocks A B C D *ᵥ Sum.elim x 0 = fromBlocks A B C D *ᵥ Sum.elim 0 0 := by
        simp [fromBlocks_mulVec, hAx, hCx]
      have hu := (isUnit_iff_isUnit_det _).2 (SymplecticGroup.symplectic_det hσ)
      exact (Sum.elim_eq_iff.1 (mulVec_injective_iff_isUnit.2 hu h)).1
    -- Adapt the field construction in Mathlib.LinearAlgebra.SymplecticGroup.
    obtain ⟨V, U, s, hV, hU, hP⟩ := exists_rank_normal_form C
    set P := V * C * U with P_def
    set Q := Vᵀ⁻¹ * A * U with Q_def
    let f (M : Matrix ι ι ℚ) := M.submatrix s.symm s.symm
    have hf (M : Matrix ι ι ℚ) : f M = M.submatrix s.symm s.symm := rfl
    have f_unit {M} : IsUnit M → IsUnit (f M) := (isUnit_submatrix_equiv ..).2
    have f_mul (M N : Matrix ι ι ℚ) : f (M * N) = f M * f N :=
      submatrix_mul _ _ _ _ _ s.symm.bijective
    have _ : Invertible V := hV.invertible
    have _ : Invertible U := hU.invertible
    have _ : Invertible (f Vᵀ) := (f_unit (V.isUnit_transpose.2 hV)).invertible
    have hker' (x : Fin C.rank ⊕ Fin (Fintype.card ι - C.rank) → ℚ)
        (hQx : f Q • x = 0) (hPx : f P • x = 0) : x = 0 := by
      refine (f_unit hU).smul_left_cancel.1 ?_
      rw [f_mul, f_mul, mul_assoc, mul_smul, IsUnit.smul_eq_zero, mul_smul, hf,
        smul_eq_mulVec, submatrix_mulVec_equiv, Equiv.symm_symm] at hQx hPx
      · rw [Equiv.comp_symm_eq, Pi.zero_comp] at hQx hPx
        exact s.surjective.injective_comp_right <| by simpa using hker _ hQx hPx
      · exact f_unit hV
      · exact f_unit <| isUnit_nonsing_inv_iff.2 <| V.isUnit_transpose.2 hV
    have hsymm : Qᵀ * P = Pᵀ * Q := by
      simp only [P_def, mul_assoc, transpose_mul, transpose_nonsing_inv, transpose_transpose,
        Q_def, inv_mul_cancel_left_of_invertible, mul_inv_cancel_left_of_invertible]
      rw [← mul_assoc Aᵀ, hb, mul_assoc]
    have hblocks : (f Q).toBlocks₁₁ᵀ = (f Q).toBlocks₁₁ ∧ (f Q).toBlocks₁₂ = 0 := by
      apply_fun reindex s s at hsymm
      rw [reindex_apply, reindex_apply, ← hf, ← hf, f_mul, f_mul Pᵀ, hP, hf,
        ← transpose_submatrix, ← hf Q, ← (f Q).fromBlocks_toBlocks, hf (_)ᵀ, hf
        ((fromBlocks 1 0 0 0).submatrix _ _)] at hsymm
      simp [fromBlocks_transpose, fromBlocks_multiply] at hsymm
      tauto
    have hunit : IsUnit (f Q).toBlocks₂₂ := by
      refine mulVec_injective_iff_isUnit.1 ?_
      rw [← coe_mulVecLin, ← LinearMap.ker_eq_bot]
      refine ker_mulVecLin_eq_bot_iff.2 fun x hx ↦ Sum.elim_injective' <|
        (hker' _ ?_ ?_).trans Sum.elim_zero_zero.symm
      · rw [← (f Q).fromBlocks_toBlocks]
        simp [hx, hblocks.2, fromBlocks_mulVec]
      · simp [hf, hP, fromBlocks_mulVec]
    set Y : Matrix (Fin C.rank ⊕ Fin (Fintype.card ι - C.rank))
        (Fin C.rank ⊕ Fin (Fintype.card ι - C.rank)) ℚ :=
      fromBlocks (1 - (f Q).toBlocks₁₁) 0 0 0 with Y_def
    have hY : Y.IsSymm := by
      rw [Y_def, isSymm_fromBlocks_iff]
      exact ⟨IsSymm.sub isSymm_one hblocks.1, by simp⟩
    set X := f Vᵀ * Y * f V with X_def
    refine ⟨X.submatrix s s, IsSymm.submatrix ?_ s, (isUnit_iff_isUnit_det _).1
      ((isUnit_submatrix_equiv s.symm s.symm).1 ?_)⟩
    · simp_rw [X_def, Matrix.IsSymm, transpose_mul, hY.eq, hf, transpose_submatrix,
        transpose_transpose, mul_assoc]
    · have heq : f (A + X.submatrix s s * C) = f Vᵀ * (f Q + Y * f P) * f U⁻¹ := by
        simp_rw [hf, submatrix_add, Pi.add_apply, Q_def, P_def, ← hf, f_mul, hf, mul_add,
          ← mul_assoc, ← inv_submatrix_equiv, add_mul, mul_assoc _ (U.submatrix _ _),
          mul_inv_of_invertible]
        simp [X_def]
        rfl
      rw [← hf, heq, IsUnit.mul_iff, IsUnit.mul_iff]
      refine ⟨⟨isUnit_of_invertible _, ?_⟩, f_unit (isUnit_nonsing_inv_iff.2 hU)⟩
      nth_rw 1 [Y_def, hP, ← (f Q).fromBlocks_toBlocks, hblocks.2]
      simpa [hf, fromBlocks_multiply, fromBlocks_add]
  obtain ⟨X, hX, hu⟩ := hex
  have h1 : (A + X * C)ᵀ * C = Cᵀ * (A + X * C) := by
    rw [transpose_add, transpose_mul, hX.eq, add_mul, mul_add, hb, Matrix.mul_assoc]
  generalize hc : A + X * C = c at hu h1
  have hcT : IsUnit cᵀ.det := by rwa [det_transpose]
  have hY : (C * c⁻¹).IsSymm := by
    unfold Matrix.IsSymm
    rw [transpose_mul, transpose_nonsing_inv]
    calc cᵀ⁻¹ * Cᵀ = cᵀ⁻¹ * (Cᵀ * c) * c⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
      _ = C * c⁻¹ := by rw [← h1, nonsing_inv_mul_cancel_left _ _ hcT]
  have hY' : C * c⁻¹ * c = C := nonsing_inv_mul_cancel_right _ _ hu
  generalize C * c⁻¹ = Y at hY hY'
  have hJ := SymplecticGroup.J_mem ι ℚ
  refine ⟨fromBlocks 1 (-X) 0 1, unip_mem_symplecticGroup hX.neg,
    fromBlocks 1 (-Y) 0 1, unip_mem_symplecticGroup hY.neg,
    J ι ℚ * fromBlocks 1 Y 0 1 * J ι ℚ * fromBlocks 1 X 0 1 * fromBlocks A B C D,
    mul_mem (mul_mem (mul_mem (mul_mem hJ (unip_mem_symplecticGroup hY)) hJ)
      (unip_mem_symplecticGroup hX)) hσ, by simp, by simp, ?_, ?_⟩
  · rw [Matrix.mul_assoc _ _ (fromBlocks A B C D), fromBlocks_multiply]
    simp only [Matrix.one_mul, hc]
    simp [J, fromBlocks_multiply, hY']
  · have e1 : (fromBlocks 1 (-Y) 0 1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) * fromBlocks 1 Y 0 1 = 1 := by
      simp [fromBlocks_multiply]
    have e2 : (fromBlocks 1 (-X) 0 1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) * fromBlocks 1 X 0 1 = 1 := by
      simp [fromBlocks_multiply]
    have e3 := J_squared ι ℚ
    generalize (fromBlocks 1 (-Y) 0 1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) = y' at e1 ⊢
    generalize (fromBlocks 1 Y 0 1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) = y at e1 ⊢
    generalize (fromBlocks 1 (-X) 0 1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) = x' at e2 ⊢
    generalize (fromBlocks 1 X 0 1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) = x at e2 ⊢
    generalize fromBlocks A B C D = s
    generalize J ι ℚ = j at e3 ⊢
    have e4 : ∀ m, j * (j * m) = -m := fun m => by rw [← mul_assoc, e3, neg_one_mul]
    have e5 : ∀ m, y' * (y * m) = m := fun m => by rw [← mul_assoc, e1, one_mul]
    have e6 : ∀ m, x' * (x * m) = m := fun m => by rw [← mul_assoc, e2, one_mul]
    simp only [mul_assoc, e4, mul_neg, e5, neg_neg, e6]

end GlobalTheory.SW
