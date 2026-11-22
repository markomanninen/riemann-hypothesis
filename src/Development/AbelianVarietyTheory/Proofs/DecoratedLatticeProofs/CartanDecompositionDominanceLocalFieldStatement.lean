module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanDecompositionDominanceLocalField
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartan_decomposition_dominance_local_field :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N : ℕ) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
      ∀ (μ ν : Fin N → ℤ), Antitone μ → Antitone ν → ∀ n : ℕ, n ≤ N → ∀ g : GL (Fin N) k,
      (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N),
        g = κ * GlobalTheory.GLDoubling.torusElt (k := k) (n := Fin N) ϖ
          (indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n)) * κ') →
      (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N),
        GlobalTheory.GLDoubling.torusElt (k := k) (n := Fin N) ϖ μ * g =
          κ * GlobalTheory.GLDoubling.torusElt (k := k) (n := Fin N) ϖ ν * κ') →
      ∑ i, ν i = ∑ i, μ i + n ∧ ∀ j : ℕ,
        ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), ν i ≤
          ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j),
            (μ i + indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n) i) := by
  intro k _ _ _ _ N ϖ hϖ μ ν hμ _ n hn g hg hmain
  let ε := indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n)
  let T := GlobalTheory.GLDoubling.torusElt (k := k) (n := Fin N) ϖ
  change ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), g = κ * T ε * κ' at hg
  change ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), T μ * g = κ * T ν * κ' at hmain
  obtain ⟨κ, hκ, κ', hκ', rfl⟩ := hg
  obtain ⟨κ₁, hκ₁, κ₂, hκ₂, hdecomp⟩ := hmain
  have hϖ₀ : 0 < valuation k (ϖ : k) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ϖ.ne_zero)
  have hϖ₁ : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hT (e : Fin N → ℤ) : (T e).1 = diagonal (fun i => (ϖ : k) ^ e i) :=
    GlobalTheory.GLDoubling.val_torusElt ..
  have hsum : ∑ i, ν i = ∑ i, μ i + ∑ i, ε i := by
    have hdet (e : Fin N → ℤ) : valuation k (T e).1.det = valuation k (ϖ : k) ^ ∑ i, e i := by
      rw [hT, det_diagonal, GlobalTheory.CartanDom.val_torus_prod]
    have h := congrArg (fun x : GL (Fin N) k => valuation k x.1.det) hdecomp
    simp only [Units.val_mul, det_mul, map_mul] at h
    rw [hdet, hdet, GlobalTheory.CartanDom.KO_det hκ, GlobalTheory.CartanDom.KO_det hκ',
      GlobalTheory.CartanDom.KO_det hκ₁, GlobalTheory.CartanDom.KO_det hκ₂] at h
    simp only [hdet, mul_one, one_mul] at h
    rw [← zpow_add₀ hϖ₀.ne'] at h
    exact le_antisymm ((zpow_le_zpow_iff_right_of_lt_one₀ hϖ₀ hϖ₁).1 h.le)
      ((zpow_le_zpow_iff_right_of_lt_one₀ hϖ₀ hϖ₁).1 h.ge)
  have hε : Antitone ε := GlobalTheory.CartanDom.indic_antitone N n
  have hcard : ∑ i, ε i = n := GlobalTheory.CartanDom.sum_indic N n hn
  refine ⟨hsum.trans (congrArg ((∑ i, μ i) + ·) hcard), fun j => ?_⟩
  let tail := Finset.univ.filter (fun i : Fin N => ¬ (i : ℕ) < j)
  have htail : (∑ i ∈ tail, μ i) + (∑ i ∈ tail, ε i) ≤ ∑ i ∈ tail, ν i := by
    by_cases hj : j < N
    swap
    · have hempty : tail = ∅ := by
        ext i
        simp [tail]
        omega
      simp [hempty]
    let I := {i : Fin N // ¬ (i : ℕ) < j}
    have hA (f h : I → Fin N) :
        valuation k (((T ε).1 * κ'.1).submatrix f h).det ≤
          valuation k (ϖ : k) ^ (∑ i ∈ tail, ε i) * 1 := by
      rw [hT]
      exact GlobalTheory.CartanDom.tail_diag ϖ hϖ ε hε j hj κ'.1 1
        (fun f h => GlobalTheory.CartanDom.val_det_le_one _
          (fun a b => GlobalTheory.CartanDom.KO_int hκ' (f a) (h b))) f h
    have hB (f h : I → Fin N) :
        valuation k ((κ * T ε * κ').1.submatrix f h).det ≤
          valuation k (ϖ : k) ^ (∑ i ∈ tail, ε i) * 1 := by
      rw [Units.val_mul, Units.val_mul, mul_assoc]
      exact GlobalTheory.CartanDom.minor_int_mul _ _ _ (GlobalTheory.CartanDom.KO_int hκ) hA f h
    have hC (f h : I → Fin N) :
        valuation k ((T μ * (κ * T ε * κ')).1.submatrix f h).det ≤
          valuation k (ϖ : k) ^ (∑ i ∈ tail, μ i) *
            (valuation k (ϖ : k) ^ (∑ i ∈ tail, ε i) * 1) := by
      rw [Units.val_mul (T μ), hT]
      exact GlobalTheory.CartanDom.tail_diag ϖ hϖ μ hμ j hj _ _ hB f h
    have hνdecomp : T ν = κ₁⁻¹ * (T μ * (κ * T ε * κ')) * κ₂⁻¹ := by
      rw [hdecomp]
      group
    have hD (f h : I → Fin N) :
        valuation k ((T ν).1.submatrix f h).det ≤
          valuation k (ϖ : k) ^ (∑ i ∈ tail, μ i) *
            (valuation k (ϖ : k) ^ (∑ i ∈ tail, ε i) * 1) := by
      rw [hνdecomp, Units.val_mul, Units.val_mul]
      exact GlobalTheory.CartanDom.minor_mul_int _ _ _ (GlobalTheory.CartanDom.KO_int (inv_mem hκ₂))
        (GlobalTheory.CartanDom.minor_int_mul _ _ _ (GlobalTheory.CartanDom.KO_int (inv_mem hκ₁)) hC) f h
    have h := hD Subtype.val Subtype.val
    rw [hT, submatrix_diagonal _ _ Subtype.val_injective, det_diagonal] at h
    simp only [Function.comp_apply] at h
    rw [GlobalTheory.CartanDom.val_torus_prod, mul_one, ← zpow_add₀ hϖ₀.ne'] at h
    have hle := (zpow_le_zpow_iff_right_of_lt_one₀ hϖ₀ hϖ₁).1 h
    rwa [← Finset.sum_subtype tail (fun i => by simp [tail]) ν] at hle
  have hνsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin N => (i : ℕ) < j) ν
  have hμsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin N => (i : ℕ) < j) μ
  have hεsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin N => (i : ℕ) < j) ε
  change ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), ν i ≤
    ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), (μ i + ε i)
  rw [Finset.sum_add_distrib]
  dsimp only [tail] at htail
  linarith
