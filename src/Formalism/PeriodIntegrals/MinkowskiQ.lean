module

public import Mathlib
public import Formalism.PeriodIntegrals.Minkowski

@[expose] public section

namespace PI

def MinkowskiBoundQ : Prop :=
  ∀ (N : ℕ) (G : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℚ)), Finite G →
    Nat.card G ∣ minkowskiM N

end PI
