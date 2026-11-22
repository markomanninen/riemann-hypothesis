module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteLevelApproxOfGeometricInvariantModPo
public import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow

@[expose] public section

open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteLevel_approx_of_geometric_invariant_modPow : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k j : ℕ), 1 ≤ j → ∀ x : Ω, IsInt (p := p) x →
  (∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, Cong (p := p) k (g x) x) →
  ∃ y : Ω, IsInt (p := p) y ∧ (∃ N, ∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) ∧
    Cong (p := p) k ((T.ζ j - 1) * x) y := by
  intro p _ hp2 Ω _ _ hClo T k j hj x hx hfix
  obtain ⟨y₀, E, hy₀, hEH, huniq, hsum⟩ :=
    GlobalTheory.T.smallTraces_subgroup_galois_towerTop p Ω hp2 hClo T
      (Ggeo p Ω ⊓ ⨅ n, Gn T n) inf_le_right {x} j hj
  have hgi (g : Gal p Ω) (z : Ω) (hz : IsInt (p := p) z) : IsInt (p := p) (g z) :=
    hz.map (g : Ω →ₐ[O0 p] Ω)
  have hlevel := GlobalTheory.K5.GeoLevel.exists_level_of_fixed hClo T _
    (GlobalTheory.K5.FinLevel.sum_fixed _ E y₀ x hEH huniq)
  refine ⟨∑ g ∈ E, g (y₀ * x), IsIntegral.sum _ (fun g _ => hgi g _ (hy₀.mul hx)), hlevel, ?_⟩
  have hz : ∀ g ∈ E, ∃ z : Ω, IsInt (p := p) z ∧ g x - x = (p : Ω) ^ k * z :=
    fun g hg => hfix g (hEH g hg)
  choose! z hzi hzx using hz
  refine ⟨-∑ g ∈ E, g y₀ * z g, ?_, ?_⟩
  · exact (IsIntegral.sum _ fun g hg => (hgi g _ hy₀).mul (hzi g hg)).neg
  · rw [← hsum, Finset.sum_mul, ← Finset.sum_sub_distrib, mul_neg, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [map_mul]
    linear_combination (-(g y₀)) * hzx g hg
