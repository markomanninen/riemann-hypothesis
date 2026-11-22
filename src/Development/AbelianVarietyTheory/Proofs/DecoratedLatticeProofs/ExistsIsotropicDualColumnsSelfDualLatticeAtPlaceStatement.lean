module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsotropicDualColumnsSelfDualLatticeAtPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_dual_columns_selfDualLatticeAtPlace : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (M : AddSubgroup (Fin S.rank → AE D)), IsSDAt S v M → ∀ w ∈ intAt D (· = v), w + cA D w = ε → ∀ (b : Mx D ρ ρ) (c' : Mx D S.rank ρ), (∀ i j, b i j ∈ idAt D (· = v)) → (∀ i, (fun k => (d.jX * b) k i) ∈ M) → (∀ i, (fun k => c' k i) ∈ M) → adj c' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ) → ∃ c'' : Mx D S.rank ρ, (∀ i, (fun k => c'' k i) ∈ M) ∧ adj c'' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ) ∧ adj c'' * (gA S * c'') = 0 := by
  intro D S S₀ ρ d v ε hεε hεc hεI hε M hM w hw hwc b c' hb hc hc' hcc
  let c : Mx D S.rank ρ := d.jX * b
  change adj c' * (gA S * c) = ε • (1 : Mx D ρ ρ) at hcc
  have hcc0 : adj c * (gA S * c) = 0 := by
    dsimp only [c]
    rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) d.jX b,
      ← Matrix.mul_assoc (adj d.jX), d.gram_XX, Matrix.zero_mul, Matrix.mul_zero]
  have hcc' : adj c * (gA S * c') = ε • (1 : Mx D ρ ρ) := by
    have h := congrArg adj hcc
    rwa [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc, adj_smul, hεc, adj_one] at h
  let H : Mx D ρ ρ := adj c' * (gA S * c')
  have hHint (i j : Fin ρ) : H i j ∈ intAt D (· = v) := by
    have hgram : H i j = hermAt S (fun k => c' k j) (fun k => c' k i) := by
      simp only [H, hermAt, adj, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
        Finset.mul_sum, mul_assoc]
    rw [hgram]
    exact (hM.2.2 _ (hM.1 _ (hc' j))).1 (hc' j) _ (hc' i)
  have hεH : ε • H = H := by
    funext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (hε _).1 (hHint i j).1
  have hadjH : adj H = H := by
    dsimp only [H]
    rw [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]
  let K : Mx D ρ ρ := w • H
  have hKint (m i : Fin ρ) : K m i ∈ intAt D (· = v) := by
    change (w • H) m i ∈ intAt D (· = v)
    rw [Matrix.smul_apply, smul_eq_mul]
    exact GlobalTheory.IwaPlace.DualIso.intAt_mul_mem hw (hHint m i)
  let c'' : Mx D S.rank ρ := c' - c * K
  have hpair : adj c'' * (gA S * c) = ε • (1 : Mx D ρ ρ) := by
    dsimp only [c'']
    rw [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, hcc0, Matrix.mul_zero,
      sub_zero, hcc]
  refine ⟨c'', ?_, hpair, ?_⟩
  · intro i
    have hcol : (fun k => (c * K) k i) = ∑ m, K m i • (fun k => c k m) := by
      funext k
      simp [Matrix.mul_apply, Finset.sum_apply, mul_comm]
    change (fun k => c' k i) - (fun k => (c * K) k i) ∈ M
    rw [hcol]
    exact sub_mem (hc' i) (AddSubgroup.sum_mem _ fun m _ =>
      GlobalTheory.IwaPlace.DualIso.smul_mem_of_isSDAt hM (hKint m i) (hc m))
  · have hleft : adj c'' * (gA S * c') = H - (ε * cA D w) • H := by
      dsimp only [c'']
      rw [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, hcc']
      change H - adj (w • H) * (ε • (1 : Mx D ρ ρ)) = _
      rw [adj_smul, hadjH, mul_smul_comm, mul_one, smul_smul]
    have hsum : ε * cA D w + ε * w = ε := by
      rw [← mul_add, add_comm, hwc, hεε]
    calc
      adj c'' * (gA S * c'') =
          adj c'' * (gA S * c') - (adj c'' * (gA S * c)) * K := by
        change adj c'' * (gA S * (c' - c * K)) = _
        rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc (gA S) c K,
          ← Matrix.mul_assoc (adj c'') (gA S * c) K]
      _ = H - (ε * cA D w) • H - (ε * w) • H := by
        rw [hleft, hpair]
        change H - (ε * cA D w) • H - (ε • (1 : Mx D ρ ρ)) * (w • H) = _
        rw [smul_mul_assoc, one_mul, smul_smul]
      _ = 0 := by rw [sub_sub, ← add_smul, hsum, hεH, sub_self]
