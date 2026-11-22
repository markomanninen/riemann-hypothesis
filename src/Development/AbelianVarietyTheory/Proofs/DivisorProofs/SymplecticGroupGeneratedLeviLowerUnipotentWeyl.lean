module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks

@[expose] public section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.SpGen
open Matrix

theorem upper_unipotent_eq {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]
    (s : Matrix κ κ K) :
    (fromBlocks 1 s 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) =
      fromBlocks 0 1 (-1) 0 * fromBlocks 1 0 (-s) 1 * fromBlocks 0 1 (-1) 0 *
        fromBlocks (-1) 0 0 (-1) := by
  simp [fromBlocks_multiply]

theorem symplectic_generated_levi_lower_weyl :
    ∀ (K : Type) [Field K] (κ : Type) [Fintype κ] [DecidableEq κ] (P : Matrix (κ ⊕ κ) (κ ⊕ κ) K → Prop),
    (∀ a b, P a → P b → P (a * b)) → (∀ g h : Matrix κ κ K, gᵀ * h = 1 → P (Matrix.fromBlocks g 0 0 h)) →
    (∀ b : Matrix κ κ K, bᵀ = b → P (Matrix.fromBlocks 1 0 b 1)) → P (Matrix.fromBlocks 0 1 (-1) 0) →
    ∀ a : Matrix (κ ⊕ κ) (κ ⊕ κ) K, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 → P a := by
  intro K _ κ _ _ P hmul hlevi hlow hJ a ha
  have hup : ∀ s : Matrix κ κ K, sᵀ = s → P (fromBlocks 1 s 0 1) := by
    intro s hs
    rw [upper_unipotent_eq]
    exact hmul _ _ (hmul _ _ (hmul _ _ hJ (hlow _ (by simp [hs]))) hJ) (hlevi _ _ (by simp))
  have hJ0 : (fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) = -J κ K := by
    simp [J, fromBlocks_neg]
  have hsp : a ∈ symplecticGroup κ K := by
    rw [SymplecticGroup.mem_iff']
    rw [hJ0] at ha
    simpa [Matrix.mul_neg, Matrix.neg_mul] using ha
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, a = fromBlocks A B C D :=
    ⟨_, _, _, _, a.fromBlocks_toBlocks.symm⟩
  have hExists : ∃ X : Matrix κ κ K, X.IsSymm ∧ IsUnit (A + X * C).det := by
    -- Use the field case of Mathlib's construction in LinearAlgebra/SymplecticGroup.
    have hker (x : κ → K) (hAx : A • x = 0) (hCx : C • x = 0) : x = 0 := by
      rw [smul_eq_mulVec] at hAx hCx
      have hunit := (fromBlocks A B C D).isUnit_iff_isUnit_det.2
        (SymplecticGroup.symplectic_det hsp)
      have hzero : fromBlocks A B C D *ᵥ Sum.elim x 0 =
          fromBlocks A B C D *ᵥ Sum.elim 0 0 := by
        simp [fromBlocks_mulVec, hAx, hCx]
      exact (Sum.elim_eq_iff.1 (mulVec_injective_iff_isUnit.2 hunit hzero)).1
    have hsymm := (SymplecticGroup.fromBlocks_mem_iff.1 hsp).1
    obtain ⟨V, U, e, hV, hU, heq⟩ := exists_rank_normal_form C
    set R := V * C * U with hR
    set S := Vᵀ⁻¹ * A * U with hS
    let f := fun M : Matrix κ κ K ↦ M.submatrix e.symm e.symm
    have hf (M : Matrix κ κ K) : f M = M.submatrix e.symm e.symm := rfl
    have f_unit {M} : IsUnit M → IsUnit (f M) := (isUnit_submatrix_equiv ..).2
    have f_mul (M N) : f (M * N) = f M * f N := submatrix_mul _ _ _ _ _ e.symm.bijective
    let _ : Invertible V := hV.invertible
    let _ : Invertible U := hU.invertible
    let _ : Invertible (f Vᵀ) := (f_unit (V.isUnit_transpose.2 hV)).invertible
    have hker' (x : Fin C.rank ⊕ Fin (Fintype.card κ - C.rank) → K)
        (hxS : f S • x = 0) (hxR : f R • x = 0) : x = 0 := by
      refine (f_unit hU).smul_left_cancel.1 ?_
      rw [f_mul, f_mul, mul_assoc, mul_smul, IsUnit.smul_eq_zero, mul_smul, hf,
        smul_eq_mulVec, submatrix_mulVec_equiv, Equiv.symm_symm] at hxS hxR
      · rw [Equiv.comp_symm_eq, Pi.zero_comp] at hxS hxR
        exact e.surjective.injective_comp_right <| by simpa using hker _ hxS hxR
      · exact f_unit hV
      · exact f_unit <| isUnit_nonsing_inv_iff.2 <| V.isUnit_transpose.2 hV
    have hSR : Sᵀ * R = Rᵀ * S := by
      simp only [hR, mul_assoc, transpose_mul, transpose_nonsing_inv, transpose_transpose, hS,
        inv_mul_cancel_left_of_invertible, mul_inv_cancel_left_of_invertible]
      rw [← mul_assoc Aᵀ, hsymm, mul_assoc]
    have hblocks : (f S).toBlocks₁₁ᵀ = (f S).toBlocks₁₁ ∧ (f S).toBlocks₁₂ = 0 := by
      apply_fun reindex e e at hSR
      rw [reindex_apply, reindex_apply, ← hf, ← hf, f_mul, f_mul Rᵀ, heq, hf,
        ← transpose_submatrix, ← hf S, ← (f S).fromBlocks_toBlocks, hf (_)ᵀ, hf
        ((fromBlocks 1 0 0 0).submatrix _ _)] at hSR
      simp [fromBlocks_transpose, fromBlocks_multiply] at hSR
      tauto
    have h₂₂ : IsUnit (f S).toBlocks₂₂ := by
      refine mulVec_injective_iff_isUnit.1 ?_
      rw [← coe_mulVecLin, ← LinearMap.ker_eq_bot]
      refine ker_mulVecLin_eq_bot_iff.2 fun x hx ↦ Sum.elim_injective' <|
        (hker' _ ?_ ?_).trans Sum.elim_zero_zero.symm
      · rw [← (f S).fromBlocks_toBlocks]
        simp [hx, hblocks.2, fromBlocks_mulVec]
      · simp [hf, heq, fromBlocks_mulVec]
    set Y : Matrix (Fin C.rank ⊕ Fin (Fintype.card κ - C.rank))
      (Fin C.rank ⊕ Fin (Fintype.card κ - C.rank)) K :=
      fromBlocks (1 - (f S).toBlocks₁₁) 0 0 0 with hY
    have hYsymm : Y.IsSymm := by
      rw [hY, isSymm_fromBlocks_iff]
      exact ⟨IsSymm.sub isSymm_one hblocks.1, by simp⟩
    set X := f Vᵀ * Y * f V with hX
    refine ⟨X.submatrix e e, IsSymm.submatrix ?_ e, (isUnit_iff_isUnit_det _).1
      ((isUnit_submatrix_equiv e.symm e.symm).1 ?_)⟩
    · simp_rw [hX, Matrix.IsSymm, transpose_mul, hYsymm.eq, hf, transpose_submatrix,
        transpose_transpose, mul_assoc]
    · have hsum : f (A + X.submatrix e e * C) = f Vᵀ * (f S + Y * f R) * f U⁻¹ := by
        simp_rw [hf, submatrix_add, Pi.add_apply, hS, hR, ← hf, f_mul, hf, mul_add, ← mul_assoc,
          ← inv_submatrix_equiv, add_mul, mul_assoc _ (U.submatrix _ _), mul_inv_of_invertible]
        simp [hX]
        rfl
      rw [← hf, hsum, IsUnit.mul_iff, IsUnit.mul_iff]
      refine ⟨⟨isUnit_of_invertible _, ?_⟩, f_unit (isUnit_nonsing_inv_iff.2 hU)⟩
      nth_rw 1 [hY, heq, ← (f S).fromBlocks_toBlocks, hblocks.2]
      simpa [hf, fromBlocks_multiply, fromBlocks_add] using h₂₂
  obtain ⟨X, hX, hu⟩ := hExists
  have hUX : (fromBlocks 1 X 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) ∈ symplecticGroup κ K := by
    simp [SymplecticGroup.fromBlocks_mem_iff, hX.eq]
  have hprod : (fromBlocks 1 X 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks A B C D =
      fromBlocks (A + X * C) (B + X * D) C D := by
    simp [fromBlocks_multiply]
  generalize hc : A + X * C = c at hu hprod
  have hcT : IsUnit cᵀ.det := by rwa [det_transpose]
  have hLev : (fromBlocks c⁻¹ 0 0 cᵀ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) ∈ symplecticGroup κ K := by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    refine ⟨by simp, by simp, ?_⟩
    rw [transpose_nonsing_inv]
    simp [nonsing_inv_mul _ hcT]
  have hnsp := mul_mem (mul_mem hLev hUX) hsp
  have hn : (fromBlocks c⁻¹ 0 0 cᵀ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks 1 X 0 1 *
      fromBlocks A B C D = fromBlocks 1 (c⁻¹ * (B + X * D)) (cᵀ * C) (cᵀ * D) := by
    rw [Matrix.mul_assoc, hprod, fromBlocks_multiply]
    simp [nonsing_inv_mul _ hu]
  rw [hn] at hnsp
  generalize c⁻¹ * (B + X * D) = Z at hn hnsp
  generalize cᵀ * C = Wm at hn hnsp
  generalize cᵀ * D = V at hn hnsp
  obtain ⟨h1, h2, h3⟩ := SymplecticGroup.fromBlocks_mem_iff.1 hnsp
  simp only [transpose_one, Matrix.one_mul, Matrix.mul_one] at h1 h3
  have hW : Wmᵀ = Wm := h1.symm
  rw [hW] at h3
  have hV : V = Wm * Z + 1 := by rw [← h3]; abel
  have hZ : Zᵀ = Z := by
    rw [hV, transpose_add, transpose_mul, hW, transpose_one, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, Matrix.one_mul, ← Matrix.mul_assoc] at h2
    simpa using h2
  have hfac : (fromBlocks 1 Z Wm V : Matrix (κ ⊕ κ) (κ ⊕ κ) K) =
      fromBlocks 1 0 Wm 1 * fromBlocks 1 Z 0 1 := by
    rw [fromBlocks_multiply, hV]; simp
  have e2 : (fromBlocks c 0 0 cᵀ⁻¹ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks c⁻¹ 0 0 cᵀ = 1 := by
    rw [fromBlocks_multiply]
    simp [mul_nonsing_inv _ hu, nonsing_inv_mul _ hcT]
  have e3 : (fromBlocks 1 (-X) 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks 1 X 0 1 = 1 := by
    simp [fromBlocks_multiply]
  have hdec : fromBlocks A B C D = (fromBlocks 1 (-X) 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) *
      fromBlocks c 0 0 cᵀ⁻¹ * (fromBlocks c⁻¹ 0 0 cᵀ * fromBlocks 1 X 0 1 * fromBlocks A B C D) := by
    rw [Matrix.mul_assoc (fromBlocks 1 (-X) 0 1), ← Matrix.mul_assoc (fromBlocks c 0 0 cᵀ⁻¹),
      ← Matrix.mul_assoc (fromBlocks c 0 0 cᵀ⁻¹), e2, Matrix.one_mul, ← Matrix.mul_assoc, e3,
      Matrix.one_mul]
  rw [hdec, hn, hfac]
  refine hmul _ _ (hmul _ _ (hup _ (by simp [hX.eq])) (hlevi _ _ ?_)) (hmul _ _ (hlow _ hW) (hup _ hZ))
  exact mul_nonsing_inv _ hcT

end GlobalTheory.SpGen
