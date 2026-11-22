module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
public import Development.AbelianVarietyTheory.Definitions.Divisors.BlockSphereMeanLinForm

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField

namespace GlobalTheory.ChowHt

attribute [local instance] MvPolynomial.gradedAlgebra

theorem aeval_smul_of_isHomogeneous {k K : Type} [Field k] [Field K] [Algebra k K] {N d : ℕ}
    {g : MvPolynomial (Fin N) k} (hg : g.IsHomogeneous d) (t : K) (z : Fin N → K) :
    aeval (t • z) g = t ^ d * aeval z g := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h := hg (mem_support_iff.1 hs)
  have hd : ∑ i, s i = d := by
    rw [← h, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hd]
  ring



end GlobalTheory.ChowHt
