module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussE

@[expose] public section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

variable {n : ℕ}

theorem cocycleZ : CocycleZ := by
  intro n e p q y y' Z hZ
  have hg := inG_mR y'
  have hnonzero {v : Fin n → ℂ} (hv : v ≠ 0) : star v ⬝ᵥ ((Z - Zᴴ) *ᵥ v) ≠ 0 := by
    intro hz
    have hpos := Matrix.PosDef.dotProduct_mulVec_pos hZ hv
    rw [smul_mulVec, dotProduct_smul, hz, smul_zero] at hpos
    exact (lt_irrefl (0 : ℂ)) hpos
  have hden (X : Matrix (Fin n) (Fin n) ℂ) :
      ¬ IsUnit ((mR y').toBlocks₂₁ * X + (mR y').toBlocks₂₂).det →
        ∃ v : Fin n → ℂ, v ≠ 0 ∧ star v ⬝ᵥ ((Xᴴ - X) *ᵥ v) = 0 := by
    rw [isUnit_iff_ne_zero, not_not]
    intro hdet
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    refine ⟨v, hv, ?_⟩
    rw [← identG hg X X, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hMv, mulVec_zero,
      dotProduct_sub, dotProduct_zero, dotProduct_mulVec, ← star_mulVec, hMv]
    simp
  have hD : IsUnit ((mR y').toBlocks₂₁ * Z + (mR y').toBlocks₂₂).det := by
    by_contra h
    obtain ⟨v, hv, hz⟩ := hden Z h
    apply hnonzero hv
    rw [← neg_sub, neg_mulVec, dotProduct_neg, hz, neg_zero]
  have hDh : IsUnit ((mR y').toBlocks₂₁ * Zᴴ + (mR y').toBlocks₂₂).det := by
    by_contra h
    obtain ⟨v, hv, hz⟩ := hden Zᴴ h
    exact hnonzero hv (by simpa only [conjTranspose_conjTranspose] using hz)
  have hW : IsSiegel (actZ y' Z) := by
    have hid := identG hg Z Z
    unfold IsSiegel actZ
    unfold IsSiegel at hZ
    set N := (mR y').toBlocks₁₁ * Z + (mR y').toBlocks₁₂
    set M := (mR y').toBlocks₂₁ * Z + (mR y').toBlocks₂₂
    have hMM : M * M⁻¹ = 1 := mul_nonsing_inv _ hD
    have hMM' : ∀ X : Matrix (Fin n) (Fin n) ℂ, (M⁻¹)ᴴ * (Mᴴ * X) = X := by
      intro X
      rw [← Matrix.mul_assoc, ← conjTranspose_mul, hMM, conjTranspose_one, Matrix.one_mul]
    have hZZ : Mᴴ * N - Nᴴ * M = Z - Zᴴ := by
      rw [← neg_sub, hid, neg_sub]
    have key : -(Complex.I / 2) • (N * M⁻¹ - (N * M⁻¹)ᴴ) =
        (M⁻¹)ᴴ * (-(Complex.I / 2) • (Z - Zᴴ)) * M⁻¹ := by
      rw [← hZZ, conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      rw [Matrix.mul_sub, Matrix.sub_mul]
      simp only [Matrix.mul_assoc, hMM, Matrix.mul_one, hMM']
    rw [key]
    exact hZ.conjTranspose_mul_mul_same
      (mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr (isUnit_nonsing_inv_det _ hD)))
  have e1 : actZ y' Z * (toBlocks₂₁ (mR y') * Z + toBlocks₂₂ (mR y')) =
      toBlocks₁₁ (mR y') * Z + toBlocks₁₂ (mR y') := by
    unfold actZ
    exact Matrix.nonsing_inv_mul_cancel_right _ _ hD
  have e2 : (actZ y' Z)ᴴ * (toBlocks₂₁ (mR y') * Zᴴ + toBlocks₂₂ (mR y')) =
      toBlocks₁₁ (mR y') * Zᴴ + toBlocks₁₂ (mR y') := by
    have hid := identG hg Z Zᴴ
    rw [sub_self] at hid
    have hDstar : IsUnit ((mR y').toBlocks₂₁ * Z + (mR y').toBlocks₂₂)ᴴ.det := by
      rw [det_conjTranspose]
      exact hD.star
    unfold actZ
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc, sub_eq_zero.mp hid,
      nonsing_inv_mul_cancel_left _ _ hDstar]
  obtain ⟨n1, n2⟩ := num_den_mul (mR y) (mR y') Z _ e1
  obtain ⟨-, n3⟩ := num_den_mul (mR y) (mR y') Zᴴ _ e2
  refine ⟨hD, hDh, hW, ?_, ?_⟩
  · show ((mR (y * y')).toBlocks₁₁ * Z + (mR (y * y')).toBlocks₁₂) *
        ((mR (y * y')).toBlocks₂₁ * Z + (mR (y * y')).toBlocks₂₂)⁻¹ = actZ y (actZ y' Z)
    rw [mR_mul, n1, n2, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc (toBlocks₂₁ (mR y') * Z + toBlocks₂₂ (mR y')),
      Matrix.mul_nonsing_inv _ hD, Matrix.one_mul]
    rfl
  · simp only [jF]
    rw [mR_mul, n2, n3, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, mul_zpow, mul_zpow, mul_zpow]
    ring

end PositivityTheory.Rg.Sw.Glob

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem actZ_K {k : GR n} (hk : InK (mR k)) : actZ k (Complex.I • 1) = Complex.I • 1 := by
  obtain ⟨hC, hD⟩ := inK_blocks hk
  have hI : IsSiegel (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    unfold IsSiegel
    have hs : -(Complex.I / 2) * (Complex.I - star Complex.I) = 1 := by
      rw [Complex.star_def, Complex.conj_I]
      linear_combination (-1 : ℂ) * Complex.I_sq
    rw [conjTranspose_smul, conjTranspose_one, ← sub_smul, smul_smul, hs, one_smul]
    exact Matrix.PosDef.one
  have hu := (cocycleZ n 0 0 0 k k _ hI).1
  have key : toBlocks₁₁ (mR k) * (Complex.I • 1) + toBlocks₁₂ (mR k) =
      (Complex.I • 1) * (toBlocks₂₁ (mR k) * (Complex.I • 1) + toBlocks₂₂ (mR k)) := by
    rw [hC, hD]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_add, smul_neg,
      smul_smul, Complex.I_mul_I, neg_smul, one_smul, neg_neg]
    abel
  unfold actZ
  rw [key, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

def mkGR (M : M2 n) (hM : M.det ≠ 0) (hG : InG M) : GR n := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hM, hG⟩

theorem mR_mkGR (M : M2 n) (hM : M.det ≠ 0) (hG : InG M) : mR (mkGR M hM hG) = M := rfl

theorem inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : InG (nU b) := by
  unfold InG nU JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hb]

theorem inG_mM {a : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit a.det) : InG (mM a) := by
  have ha' : IsUnit aᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact ha.star
  unfold InG mM JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Matrix.conjTranspose_nonsing_inv, Matrix.mul_nonsing_inv _ ha', Matrix.nonsing_inv_mul _ ha]

theorem det_nU (b : Matrix (Fin n) (Fin n) ℂ) : (nU b).det = 1 := by
  simp [nU]

theorem det_mM {a : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit a.det) : (mM a).det ≠ 0 := by
  have ha' : IsUnit aᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact ha.star
  unfold mM
  rw [Matrix.det_fromBlocks_zero₂₁]
  exact (ha.mul (Matrix.isUnit_nonsing_inv_det _ ha')).ne_zero

end PositivityTheory.Rg.Sw.Glob.GaussH
