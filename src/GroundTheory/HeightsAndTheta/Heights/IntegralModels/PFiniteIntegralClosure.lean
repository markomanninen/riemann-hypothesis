module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteIntegralClosureCharP
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteIntegralClosureCharZero

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

theorem FiniteIntegralClosure.proof : FiniteIntegralClosure.Statement := by
  intro A _ _ _ K _ _ _ L _ _ _ _ _
  obtain ⟨p, hp⟩ := CharP.exists A
  rcases CharP.char_is_prime_or_zero A p with hp' | rfl
  · have : Fact p.Prime := ⟨hp'⟩
    exact finite_integralClosure_of_charP p A K L
  · have : CharZero A := CharP.charP_to_charZero A
    exact finite_integralClosure_of_charZero A K L

end GroundTheory.Heights₂.Heights.Model
