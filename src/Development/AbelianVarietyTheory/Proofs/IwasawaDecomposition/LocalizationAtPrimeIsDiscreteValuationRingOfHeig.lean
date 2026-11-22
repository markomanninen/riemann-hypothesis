module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive

@[expose] public section

namespace GlobalTheory

theorem localizationAtPrime_isDiscreteValuationRing_of_height_eq_one :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      (q : Ideal A) [q.IsPrime], q.height = 1 → IsDiscreteValuationRing (Localization.AtPrime q) := by
  intro A _ _ _ _ q _ hq
  exact isDiscreteValuationRing_of_height_eq_one q hq (Localization.AtPrime q)

end GlobalTheory
