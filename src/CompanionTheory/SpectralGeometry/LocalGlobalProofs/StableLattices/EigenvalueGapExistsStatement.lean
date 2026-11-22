module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EigenvalueGapExists

@[expose] public section

theorem _root_.GlobalTheory.T.exists_gap_interval_avoiding_finite_family : ∀ (n : ℕ) (l : Fin n → ℝ) (L : ℝ), 0 < L → (∀ i, 0 ≤ l i ∧ l i ≤ L) → (∃ i, l i = L) → ∃ r : ℕ, r < n ∧ ∀ i, l i < r * (L / (n + 1)) ∨ (r + 1) * (L / (n + 1)) ≤ l i := by
  exact GlobalTheory.CompanionTheory.UGeoGap.exists_gap_of_mem_Icc_top
