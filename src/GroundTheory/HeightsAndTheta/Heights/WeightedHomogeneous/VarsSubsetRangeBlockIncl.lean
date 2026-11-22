module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Examples
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.DualModel
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [Fintype ι] [DecidableEq ι] in
theorem blockIncl_injective (k₀ : ι) : Function.Injective (blockIncl (n := n) k₀) := by
  rintro ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩ h
  simp only [blockIncl, Sigma.mk.injEq, heq_eq_eq, true_and] at h
  subst h; rfl




end

end GroundTheory.Heights₂.Heights
