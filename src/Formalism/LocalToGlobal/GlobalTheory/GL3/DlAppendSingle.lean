module

public import Mathlib
public import Formalism.LocalToGlobal.GlobalTheory.GL3.IntegralityIffAwayAtD

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

section Pd

variable {σ : Type*} {p : ℕ} [Fact p.Prime]

end Pd

section Der

variable {D : D7} {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

variable {lam}

theorem isPadicIntegral_add {x y : ℂ_[p]} (hx : IsIntP x) (hy : IsIntP y) : IsIntP (x + y) :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

end Der

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC
