module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped ComplexOrder

namespace Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {m n : ℕ}

section Subst

def dExp (m : ℕ) (p : D.what₂.Tau → ℕ) (e : D.what₂.Tau → ℤ) (τ : D.what₂.Tau) : ℤ := (p τ : ℤ) - ((m + 1) / 2 : ℕ) - e τ

end Subst

section Equiv

end Equiv

end Formalism.IndefR.Datum

end
