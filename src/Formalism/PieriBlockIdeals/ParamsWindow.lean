module

public import Mathlib
public import Formalism.RankGapBounds.CloudMinFalse

@[expose] public section

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

def lamOf (N : ℕ) (U : ℕ → ℤ) (i : ℕ) : ℤ := U i - ((N : ℤ) - 1 - (i : ℤ))

end Formalism.CohomologicalDescent
