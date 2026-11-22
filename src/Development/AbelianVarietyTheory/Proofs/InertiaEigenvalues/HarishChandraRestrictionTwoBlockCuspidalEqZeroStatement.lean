module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraRestrictionTwoBlockCuspidalEqZero
public import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

@[expose] public section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraRestrictionTwoBlock_cuspidal_eq_zero : ∀ (g : ℕ) [Fact g.Prime] (d a : ℕ) (χ : Gn g d → ℂ), IsCusp χ → 0 < a → a < d → ∀ x y, res a (d - a) χ x y = 0 := by
  first | exact @GlobalTheory.GLq.res_cusp_eq_zero | exact GlobalTheory.GLq.res_cusp_eq_zero | (intros; apply GlobalTheory.GLq.res_cusp_eq_zero <;> assumption)
