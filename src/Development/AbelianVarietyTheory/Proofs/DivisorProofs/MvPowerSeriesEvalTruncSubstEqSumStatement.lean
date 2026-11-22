module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesEvalTruncSubstEqSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_eval_trunc_subst_eq_sum :
    ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (σ τ : Type) [Fintype σ] [DecidableEq σ]
      [Fintype τ] [DecidableEq τ] (z : σ → B) (u : τ → MvPowerSeries σ B),
      (∀ j, constantCoeff (u j) = 0) → ∀ (g : MvPowerSeries τ Q) (n : σ →₀ ℕ)
      (S : Finset (τ →₀ ℕ)), (∀ α : τ →₀ ℕ, α.degree ≤ n.degree → α ∈ S) →
      MvPolynomial.eval (fun i => algebraMap B Q (z i))
        (trunc' Q n (MvPowerSeries.subst (σ := τ) (τ := σ) (R := Q) (S := Q) (up Q u) g)) =
        ∑ α ∈ S, coeff α g *
          algebraMap B Q (MvPolynomial.eval z (trunc' B n (α.prod fun j e => u j ^ e))) := by
  intro B Q _ _ _ σ τ _ _ _ _ z u hu g n S hS
  have ha : HasSubst (up Q u) :=
    hasSubst_of_constantCoeff_zero fun j => by simp [up, constantCoeff_map, hu j]
  have hprod (α : τ →₀ ℕ) : (α.prod fun j e => up Q u j ^ e) =
      map (algebraMap B Q) (α.prod fun j e => u j ^ e) := by
    rw [map_finsuppProd]
    simp [up, map_pow]
  have hcoeff (β : σ →₀ ℕ) (hβ : β ≤ n) :
      coeff β (MvPowerSeries.subst (σ := τ) (τ := σ) (R := Q) (S := Q) (up Q u) g) =
        ∑ α ∈ S, coeff α g * algebraMap B Q (coeff β (α.prod fun j e => u j ^ e)) := by
    rw [coeff_subst ha]
    simp_rw [hprod, coeff_map, smul_eq_mul]
    apply finsum_eq_sum_of_support_subset
    intro α hα
    by_contra hαS
    apply hα
    dsimp only
    have hlt : n.degree < α.degree := lt_of_not_ge fun h => hαS (hS α h)
    rw [GlobalTheory.T.coeff_finsuppProd_constFree_eq_zero_of_degree_lt B σ τ u hu α β
      (lt_of_le_of_lt (Finsupp.degree_mono hβ) hlt), map_zero, mul_zero]
  rw [GlobalTheory.DivSub.eval_trunc'_eq_sum, Finset.sum_congr rfl fun β hβ => by
    rw [hcoeff β (Finset.mem_Iic.mp hβ)]]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GlobalTheory.DivSub.eval_trunc'_eq_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_mul, map_prod]
  simp_rw [map_pow]
  ring
