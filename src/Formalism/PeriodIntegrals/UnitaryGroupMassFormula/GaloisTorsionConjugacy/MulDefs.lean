module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.StAddRight

@[expose] public section

noncomputable section

namespace PI.GalTorsConj.W

open Formalism.L2.Th1.F

def ExtRho : Prop :=
  ∀ (M M₁ : IntermediateField ℚ ℂ) (h : M ≤ M₁), (∀ x ∈ M₁, IsAlgebraic M x) →
    ∀ ρ : M →ₐ[ℚ] ℂ, ∃ ρ₁ : M₁ →ₐ[ℚ] ℂ, ∀ x : M, ρ₁ (IntermediateField.inclusion h x) = ρ x

end PI.GalTorsConj.W

end
