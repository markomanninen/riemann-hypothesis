module

public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.BaseSt
public import Mathlib
public import Formalism.LocalRingCardinality.DataCD

@[expose] public section

noncomputable section

open Formalism.BasicNotions MeasureTheory

namespace Formalism.IndefR.Eqv

theorem minfDensity_ne_zero (N : ℕ) : Formalism.L2.Theta.minfDensity N ≠ 0 := by
  unfold Formalism.L2.Theta.minfDensity
  exact ENNReal.inv_ne_zero.mpr (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)

theorem minfDensity_ne_top (N : ℕ) : Formalism.L2.Theta.minfDensity N ≠ ⊤ := by
  unfold Formalism.L2.Theta.minfDensity
  exact ENNReal.inv_ne_top.mpr (pow_ne_zero _ two_ne_zero)

end Formalism.IndefR.Eqv

end
