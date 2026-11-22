module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalCharacterLabelUniqueGLn
public import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

@[expose] public section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidalCharacter_label_unique_GLn : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → ∀ (d : ℕ) (P P' : (ZMod g)[X]) (χ χ' : Gn g d → ℂ), IsCuspOf L P χ → (IsCuspOf L P' χ → P = P') ∧ (Green → IsCuspOf L P χ' → χ = χ') := by
  first | exact @GlobalTheory.GLq.isCuspOf_label_unique | exact GlobalTheory.GLq.isCuspOf_label_unique | (intros; apply GlobalTheory.GLq.isCuspOf_label_unique <;> assumption)
