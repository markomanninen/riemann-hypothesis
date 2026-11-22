module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagStabilizerEqUnipotentTorusLeviAtPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagStabilizer_eq_unipotent_torus_levi_atPlace : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (g : GA D S), g ∈ grpAt S (· = v) → (∃ a : Mx D ρ ρ, (∀ i j, j < i → a i j = 0) ∧ mt S g * d.jX = d.jX * a) → ∃ n ∈ flagN d, n ∈ grpAt S (· = v) ∧ ∃ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) ∧ d.levi t ∈ grpAt S (· = v) ∧ ∃ γ ∈ grpAt S₀ (· = v), g = n * d.levi t * d.emb0 γ := by
  intro D S S₀ ρ d v g hg ⟨a, hup, hgX⟩
  have hG' : ∀ i j, (mt S g - 1) i j ∈ idAt D (· = v) := fun i j => by
    rw [Matrix.sub_apply]; exact (mem_congGrp_iff S (idAt D (· = v)) g).1 hg i j

  have hba : (adj (mt S g * d.jY) * (gA S * d.jX)) * a = 1 := by
    have h1 : adj (mt S g * d.jY) * (gA S * (mt S g * d.jX)) = 1 := by
      rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc (adj (mt S g)), mt_unitary]
      exact d.gram_YX
    rw [hgX] at h1
    simpa only [Matrix.mul_assoc] using h1
  have hab : a * (adj (mt S g * d.jY) * (gA S * d.jX)) = 1 := mul_eq_one_comm.1 hba
  obtain ⟨A, hA⟩ : ∃ A : GL (Fin ρ) (AE D), A.1 = a := ⟨⟨a, _, hab, hba⟩, rfl⟩

  have hdet : IsUnit a.det := Matrix.isUnit_det_of_left_inverse hba
  rw [Matrix.det_of_isUpperTriangular (M := a) (fun ⦃i j⦄ h => hup i j h)] at hdet
  have hu : ∀ i, IsUnit (a i i) := fun i =>
    isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun k => a k k) (Finset.mem_univ i)) hdet
  obtain ⟨t, ht1, htinv⟩ : ∃ t : GL (Fin ρ) (AE D), t.1 = diagonal (fun i => a i i) ∧
      (t⁻¹).1 = diagonal (fun i => (((hu i).unit⁻¹ : (AE D)ˣ) : AE D)) :=
    ⟨⟨diagonal (fun i => a i i), diagonal (fun i => (((hu i).unit⁻¹ : (AE D)ˣ) : AE D)),
      by rw [diagonal_mul_diagonal]; simp only [IsUnit.mul_val_inv, diagonal_one],
      by rw [diagonal_mul_diagonal]; simp only [IsUnit.val_inv_mul, diagonal_one]⟩, rfl, rfl⟩
  have ht_diag : ∀ i j, i ≠ j → t.1 i j = 0 := fun i j h => by rw [ht1]; exact diagonal_apply_ne _ h

  have hAt : (A * t⁻¹).1 =
      a * diagonal (fun i => (((hu i).unit⁻¹ : (AE D)ˣ) : AE D)) := by
    rw [Units.val_mul A t⁻¹, htinv, hA]
  have hUX : A * t⁻¹ ∈ UX D ρ := fun i j =>
    ⟨fun h => by rw [hAt, mul_diagonal, hup i j h, zero_mul],
      by rw [hAt, mul_diagonal]; exact IsUnit.mul_val_inv (hu i)⟩
  have hR' : mt S (g * (d.levi t)⁻¹) * d.jX = d.jX * (A * t⁻¹).1 := by
    rw [Units.val_mul A t⁻¹, hA, ← map_inv d.levi t, mt_mul, Matrix.mul_assoc, d.levi_jX]
    simpa only [Matrix.mul_assoc] using congrArg (fun M : Mx D S.rank ρ => M * (t⁻¹).1) hgX
  let u := A * t⁻¹
  let r := g * (d.levi t)⁻¹
  let s := d.levi u⁻¹ * r
  have hsX : mt S s * d.jX = d.jX := by
    change mt S (d.levi u⁻¹ * r) * d.jX = d.jX
    rw [mt_mul, Matrix.mul_assoc, show mt S r * d.jX = d.jX * u.1 from hR',
      ← Matrix.mul_assoc, d.levi_jX, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.mul_one]
  have hgram {k l : ℕ} (X : Mx D S.rank k) (Y : Mx D S.rank l) :
      adj (mt S s * X) * (gA S * (mt S s * Y)) = adj X * (gA S * Y) := by
    rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) _ Y,
      ← Matrix.mul_assoc (adj (mt S s)), mt_unitary]
  have hsY : d.pY * (mt S s * d.j0) = 0 := by
    rw [d.pY_eq, Matrix.mul_assoc, ← hsX, hgram, d.wittDecomp_gram_X_anisotropic]
  let B := d.pX * (mt S s * d.j0)
  let Q := d.p0 * (mt S s * d.j0)
  have hs0 : mt S s * d.j0 = d.jX * B + d.j0 * Q := by
    conv_lhs => rw [← Matrix.one_mul (mt S s * d.j0), ← d.sum_eq_one]
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      hsY, Matrix.mul_zero, add_zero]
  have hQ : adj Q * (gA S₀ * Q) = gA S₀ := by
    have h := hgram d.j0 d.j0
    rw [hs0, d.gram_00] at h
    simpa only [adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
      cancel₃ d.gram_XX, cancel₃ d.wittDecomp_gram_X_anisotropic, cancel₃ d.gram_0X,
      cancel₃ d.gram_00, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] using h
  let γ := GlobalTheory.MixModel.ofMat S₀ Q hQ
  have hγQ : mt S₀ γ = Q := by
    change mt S₀ (GlobalTheory.MixModel.ofMat S₀ Q hQ) = Q
    rw [mt_ofMat]
  have hs0' : mt S s * d.j0 = d.jX * B + d.j0 * mt S₀ γ := by rw [hγQ, hs0]
  let n₀ := s * (d.emb0 γ)⁻¹
  have hn₀X : mt S n₀ * d.jX = d.jX := by
    change mt S (s * (d.emb0 γ)⁻¹) * d.jX = d.jX
    rw [← map_inv, mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, hsX]
  have hn₀0 : mt S n₀ * d.j0 = d.j0 + d.jX * (B * mt S₀ γ⁻¹) := by
    change mt S (s * (d.emb0 γ)⁻¹) * d.j0 = _
    rw [← map_inv, mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic,
      ← Matrix.mul_assoc, hs0', Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc d.j0,
      GlobalTheory.MixModel.mt_mul_inv, Matrix.mul_one, add_comm]
  have hn₀ : n₀ ∈ flagN d := by
    refine d.mem_NFlag HypDec.one_mem_upperUni ?_ hn₀0
    rw [hn₀X, Units.val_one, Matrix.mul_one]
  let n := d.levi u * n₀
  have hn : n ∈ flagN d := mul_mem (d.levi_mem_NFlag hUX) hn₀
  have hnγ : g * (d.levi t)⁻¹ = n * d.emb0 γ := by
    change r = (d.levi u * (s * (d.emb0 γ)⁻¹)) * d.emb0 γ
    rw [mul_assoc, inv_mul_cancel_right]
    change r = d.levi u * (d.levi u⁻¹ * r)
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

  have hgfac : g = n * d.levi t * d.emb0 γ := by
    rw [mul_assoc, ← d.wittHyperbolic_anisotropic_commute_levi, ← mul_assoc, ← hnγ,
      inv_mul_cancel_right]

  have hmtγ : mt S₀ γ = d.p0 * (mt S g * d.j0) := by
    rw [hγQ]
    change d.p0 * (mt S (d.levi u⁻¹ * (g * (d.levi t)⁻¹)) * d.j0) = _
    rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← map_inv d.levi t,
      d.wittDecomp_levi_inclAnisotropic, ← Matrix.mul_assoc d.p0,
      d.wittDecomp_projAnisotropic_levi]
  have hγ : γ ∈ grpAt S₀ (· = v) := (mem_congGrp_iff S₀ _ γ).2 fun i j => by
    have e : mt S₀ γ - 1 = d.p0 * ((mt S g - 1) * d.j0) := by
      rw [hmtγ, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, d.p0_j0]
    rw [← Matrix.sub_apply, e]
    exact GlobalTheory.IwaFlag.mul_left_mem _ (GlobalTheory.IwaFlag.mul_right_mem _ hG') i j

  have haI : ∀ i j, (a - 1) i j ∈ idAt D (· = v) := by
    have e : a - 1 = d.pX * ((mt S g - 1) * d.jX) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, d.pX_jX, hgX, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]
    intro i j
    rw [e]
    exact GlobalTheory.IwaFlag.mul_left_mem _ (GlobalTheory.IwaFlag.mul_right_mem _ hG') i j
  have ht1I : ∀ i j, (t.1 - 1) i j ∈ idAt D (· = v) := by
    intro i j
    rw [ht1, Matrix.sub_apply]
    by_cases h : i = j
    · subst h
      have := haI i i
      rw [Matrix.sub_apply] at this
      rwa [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_zero]
      exact Ideal.zero_mem _
  have htiI : ∀ i j, ((t⁻¹).1 - 1) i j ∈ idAt D (· = v) := by
    intro i j
    rw [htinv, Matrix.sub_apply]
    by_cases h : i = j
    · subst h
      have := haI i i
      rw [Matrix.sub_apply, Matrix.one_apply_eq] at this
      rw [diagonal_apply_eq, Matrix.one_apply_eq]
      have e : (((hu i).unit⁻¹ : (AE D)ˣ) : AE D) - 1 = -((((hu i).unit⁻¹ : (AE D)ˣ) : AE D) * (a i i - 1)) := by
        rw [mul_sub, IsUnit.val_inv_mul (hu i)]; ring
      rw [e]
      exact (idAt D (· = v)).neg_mem (Ideal.mul_mem_left _ _ this)
    · rw [diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_zero]
      exact Ideal.zero_mem _
  have hadjI : ∀ i j, (adj (t⁻¹).1 - 1) i j ∈ idAt D (· = v) := by
    intro i j
    rw [← adj_one, ← adj_sub]
    exact GlobalTheory.IwaFlag.cA_mem_idAt' (htiI j i)
  have hlevI : d.levi t ∈ grpAt S (· = v) := by
    have e : mt S (d.levi t) - 1 = d.jX * (t.1 - 1) * d.pX + d.jY * (adj (t⁻¹).1 - 1) * d.pY := by
      rw [d.mt_levi, ← d.sum_eq_one]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
      abel
    refine (mem_congGrp_iff S _ _).2 fun i j => ?_
    rw [← Matrix.sub_apply, e, Matrix.add_apply]
    exact add_mem (GlobalTheory.IwaFlag.mul_right_mem _ (GlobalTheory.IwaFlag.mul_left_mem _ ht1I) i j) (GlobalTheory.IwaFlag.mul_right_mem _ (GlobalTheory.IwaFlag.mul_left_mem _ hadjI) i j)
  have hnI : n ∈ grpAt S (· = v) := by
    have hγI : d.emb0 γ ∈ grpAt S (· = v) := by
      have hγ' : ∀ i j, (mt S₀ γ - 1) i j ∈ idAt D (· = v) := fun i j => by
        rw [Matrix.sub_apply]
        exact (mem_congGrp_iff S₀ _ γ).1 hγ i j
      have e : mt S (d.emb0 γ) - 1 = d.j0 * (mt S₀ γ - 1) * d.p0 := by
        rw [d.unitaryMatrix_wittCoreEmbedding, ← d.sum_eq_one, Matrix.mul_sub, Matrix.sub_mul,
          Matrix.mul_one]
        abel
      refine (mem_congGrp_iff S _ _).2 fun i j => ?_
      rw [← Matrix.sub_apply, e]
      exact GlobalTheory.IwaFlag.mul_right_mem _ (GlobalTheory.IwaFlag.mul_left_mem _ hγ') i j
    have e : n = g * (d.levi t * d.emb0 γ)⁻¹ := eq_mul_inv_of_mul_eq ((mul_assoc _ _ _).symm.trans hgfac.symm)
    rw [e]
    exact mul_mem hg (inv_mem (mul_mem hlevI hγI))
  exact ⟨n, hn, hnI, t, ht_diag, hlevI, γ, hγ, hgfac⟩
