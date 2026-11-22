module

public import Mathlib

@[expose] public section

namespace GlobalTheory

open Finset

theorem setOf_degree_eq_coe_finsuppAntidiag (σ : Type*) [Fintype σ] [DecidableEq σ] (a : ℕ) :
    {α : σ →₀ ℕ | α.degree = a} = ↑(finsuppAntidiag (univ : Finset σ) a) := by
  ext α
  simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]

theorem ncard_degree_eq (σ : Type*) [Fintype σ] (a : ℕ) :
    {α : σ →₀ ℕ | α.degree = a}.ncard = (a + Fintype.card σ - 1).choose a := by
  classical
  rw [setOf_degree_eq_coe_finsuppAntidiag, Set.ncard_coe_finset,
    Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Nat.add_comm]

theorem natCard_degree_eq (σ : Type*) [Fintype σ] (a : ℕ) :
    Nat.card {α : σ →₀ ℕ // α.degree = a} = (a + Fintype.card σ - 1).choose a := by
  have h := ncard_degree_eq σ a
  rw [← Nat.card_coe_set_eq] at h
  exact h

end GlobalTheory
