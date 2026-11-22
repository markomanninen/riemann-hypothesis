module

public import Mathlib
public import Formalism.FormalDegreeBessel.StatementWR

@[expose] public section

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Formalism.QuantumDeterminants

theorem isOpen_OmX (m : ℕ) : IsOpen (OmX m) := by
  have h : OmX m = ⋂ l, {x : Fin m → ℂ | x l ≠ 0} := by
    ext x
    simp [OmX]
  rw [h]
  exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const

variable {m : ℕ}

end Formalism.QuantumDeterminants
