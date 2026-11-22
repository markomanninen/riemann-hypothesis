module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem specFirst_C_mul {n k : ℕ} (c : ℂ) (f : MvPolynomial (Fin (k + 1) × Fin n) ℂ) (u : Fin n → ℂ) :
    specFirst (C c * f) u = C c * specFirst f u := by
  unfold specFirst
  rw [map_mul, bind₁_C_right]

end

end GroundTheory.Heights₂.Heights
