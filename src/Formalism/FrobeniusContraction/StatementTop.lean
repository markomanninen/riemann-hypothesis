module

public import Mathlib

@[expose] public section

noncomputable section

open Classical

namespace Formalism.WachCohomologyFacts.Top

def GlobalTheory (w t : ℕ) : Finset ℤ := Finset.Icc (w : ℤ) ((w : ℤ) + t - 1)

end Formalism.WachCohomologyFacts.Top
