module

public import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
public import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
public import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

variable {C : Type} [Field C]

def IntS (V : VF C) {σ : Type} (F : MvPowerSeries σ C) : Prop :=
  ∀ μ : σ →₀ ℕ, V.Ge 0 (MvPowerSeries.coeff μ F)

end Formalism.L2.FormalSeriesBounds
