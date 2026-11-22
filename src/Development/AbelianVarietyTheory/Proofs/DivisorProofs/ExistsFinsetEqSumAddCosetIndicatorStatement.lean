module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetEqSumAddCosetIndicator
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharNegEqOne

@[expose] public section

open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_eq_sum_addCosetIndicator : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (L : AddSubgroup X), IsOpen (L : Set X) → ∀ f ∈ GlobalTheory.WeilM.SB X, (∀ Y, ∀ C ∈ L, f (Y + C) = f Y) → ∃ F : Finset X, f = ∑ y ∈ F, f y • GlobalTheory.LinSchur.cind L y := by
  first | exact @GlobalTheory.LinSchur.exists_finset_eq_sum_cind | exact GlobalTheory.LinSchur.exists_finset_eq_sum_cind | (intros; apply GlobalTheory.LinSchur.exists_finset_eq_sum_cind <;> assumption)
