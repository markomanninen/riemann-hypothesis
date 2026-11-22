module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.SharpRestriction.Divisibility.WeightFamilies

@[expose] public section

noncomputable section

namespace GlobalTheory.ConstCompare

open Formalism.BasicNotions Formalism.MainNotions NumberField

variable {D : D7}

theorem choose_two_add (p q : ℕ) :
    p * q + p * (p - 1) / 2 + q * (q - 1) / 2 = (p + q).choose 2 := by
  rw [← Nat.choose_two_right, ← Nat.choose_two_right]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← Nat.add_assoc, Nat.choose_succ_succ' (p + q) 1, Nat.choose_succ_succ' q 1, ← ih]
    simp only [Nat.choose_one_right]
    ring

end GlobalTheory.ConstCompare

end
