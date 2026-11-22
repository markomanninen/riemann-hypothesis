module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt

@[expose] public section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory

theorem exists_pdPoly : ∀ (B : Type) [CommRing B], Nonempty (PDPoly B) :=
  fun B _ ↦ ⟨stdPoly B⟩

end GlobalTheory
