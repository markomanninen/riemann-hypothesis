module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisor
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagBundle
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsHsymmShift
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.TrivBundleIsTwistedForms
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PNumericalSegre
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

set_option linter.unusedSectionVars false

namespace ProjectiveBundleNumbers

theorem sum_choose_succ (n : ℕ) (U : ℕ → ℤ) :
    ∑ k ∈ Finset.range (n + 2), ((n + 1).choose k : ℤ) * U k =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * U k +
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * U (k + 1) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun k => (n.choose k : ℤ) * U k)]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib,
    Nat.choose_zero_right]
  rw [Finset.sum_range_succ (fun k => (n.choose (k + 1) : ℤ) * U (k + 1)),
    Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
  ring

section ProjBundle

variable {K : Type*} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {F : Type*} [Field F] {Ω : Type*} [Field Ω] [Algebra F Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

end ProjBundle

section Rename

variable {F : Type} [Field F] {S : Type} [Fintype S] [DecidableEq S] {κ ι' : S → Type}
  [∀ s, Fintype (κ s)] [∀ s, Fintype (ι' s)]

end Rename

end ProjectiveBundleNumbers

end

end GroundTheory.Heights₂.Heights.NumbersDVR
