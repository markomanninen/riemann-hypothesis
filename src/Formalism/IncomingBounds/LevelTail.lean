module

public import Formalism.IncomingBounds.IncomingBound

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

def capNat (n0 y : ℕ) : ℕ := ∏ a ∈ Finset.range n0, (y + a).factorial / a.factorial

end Formalism.IncomingBounds
