module

public import Mathlib
public import Formalism.DropLevelBounds.Statement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WtAddSingle

@[expose] public section

open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators

noncomputable section

namespace GlobalTheory.UnitCase

variable {C : Type} [Field C] {σ κ : Type}

lemma jetAt0_eq_sum (P : MvPolynomial σ C) (G : MvPowerSeries σ C) (s : Finset (σ →₀ ℕ))
    (hs : P.support ⊆ s) :
    jetAt0 P G = ∑ m ∈ s, AddMonoidAlgebra.coeff P m * (mfact m : C) * MvPowerSeries.coeff m G := by
  unfold jetAt0
  refine Finset.sum_subset hs fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.1 hm]
  simp

end GlobalTheory.UnitCase
