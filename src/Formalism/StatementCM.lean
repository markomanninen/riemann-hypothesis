module

public import Formalism.StatementOC

@[expose] public section

open Finset

noncomputable section

namespace Formalism

def counts {l : ℕ} (Φ : Finset (ZMod l)ˣ) (σ : (ZMod l)ˣ) : Prop := σ ∉ Φ ∧ σ ≠ -1



end Formalism
