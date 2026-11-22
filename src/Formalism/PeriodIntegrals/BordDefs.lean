module

public import Formalism.FormalDegreeBessel.StatementBF

@[expose] public section

open Matrix

noncomputable section

namespace PI

open Formalism.QuantumDeterminants

def wbPart (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Fin (k + 1) → ℂ := fun j => v (wI k r j)

def prW (k : ℕ) (zb : Fin (k + 1) → ℂ) (v : Fin (k + 1) → ℂ) : Fin (k + 1) → ℂ :=
  v - (herm (Hb k) v zb / herm (Hb k) zb zb) • zb

end PI
