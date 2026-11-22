module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIrrCharactersAndFinsumCentralIdempotentsEq
public import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

@[expose] public section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one : ∀ (G : Type) [Group G] [Fintype G] , {χ : G → ℂ | IsIrr χ}.Finite ∧ ∑ᶠ χ ∈ {χ : G → ℂ | IsIrr χ}, zOf χ = 1 := by
  first | exact @GlobalTheory.GLq.irr_finite_and_finsum_zOf_eq_one | exact GlobalTheory.GLq.irr_finite_and_finsum_zOf_eq_one | (intros; apply GlobalTheory.GLq.irr_finite_and_finsum_zOf_eq_one <;> assumption)
