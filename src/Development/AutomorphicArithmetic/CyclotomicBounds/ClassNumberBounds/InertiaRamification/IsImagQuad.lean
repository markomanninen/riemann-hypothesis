module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.LogRootDiscChar

@[expose] public section

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ}

def IsImagQuad (ψ : DirichletCharacter ℂ N) (d : ℕ) : Prop :=
  ψ ^ 2 = 1 ∧ ψ.Odd ∧ ψ.conductor = d

end KStar.Ram
