module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraSeriesCentralIdempotentNeZero
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass

@[expose] public section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraSeriesCentralIdempotent_ne_zero : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), Green → ∀ (n : ℕ) (f : (ZMod g)[X]), f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 → eSerC L n f ≠ 0 := by
  exact @GlobalTheory.GLm.eSerC_ne_zero
