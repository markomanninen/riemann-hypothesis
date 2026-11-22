module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HoweSpanFamiliesOfPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeSpan_families_of_places : ∀ (ι : Type) [Fintype ι], HoweSpan ι := by
  first | exact @GlobalTheory.KJInf.howeSpan_all | exact GlobalTheory.KJInf.howeSpan_all | (intros; apply GlobalTheory.KJInf.howeSpan_all <;> assumption)
