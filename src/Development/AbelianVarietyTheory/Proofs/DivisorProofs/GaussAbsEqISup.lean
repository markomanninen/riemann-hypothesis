module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
public import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeAlgebraMap

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open Polynomial (nthRootsFinset)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSChoice.BaseChange

theorem gaussAbs_eq_iSup {K ι : Type} [Field K] [NumberField K] (v : FinitePlace K) (g : MvPolynomial ι K)
    (s : Finset (ι →₀ ℕ)) (hs : g.support ⊆ s) (hne : s.Nonempty) :
    gaussAbs v g = ⨆ k : s, v (AddMonoidAlgebra.coeff g (k : ι →₀ ℕ)) := by
  classical
  have : Nonempty s := hne.to_subtype
  have hsup : (g.support.sup fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal) = s.sup fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal := by
    refine le_antisymm (Finset.sup_mono hs) (Finset.sup_le fun m hm => ?_)
    by_cases hm' : m ∈ g.support
    · exact Finset.le_sup (f := fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal) hm'
    · rw [MvPolynomial.notMem_support_iff.1 hm', map_zero, Real.toNNReal_zero]
      exact bot_le
  unfold gaussAbs
  rw [hsup]
  obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup s hne fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal
  rw [hkeq, Real.coe_toNNReal _ (apply_nonneg _ _)]
  refine le_antisymm (le_ciSup (f := fun k : s => v (AddMonoidAlgebra.coeff g (k : ι →₀ ℕ))) (Set.finite_range _).bddAbove ⟨k, hk⟩)
    (ciSup_le fun m => ?_)
  have h1 : (v (AddMonoidAlgebra.coeff g (m : ι →₀ ℕ))).toNNReal ≤ (v (AddMonoidAlgebra.coeff g k)).toNNReal := by
    rw [← hkeq]; exact Finset.le_sup (f := fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal) m.2
  have h2 := (Real.toNNReal_le_toNNReal_iff (apply_nonneg _ _)).1 h1
  exact h2

end GlobalTheory.HSChoice.BaseChange
