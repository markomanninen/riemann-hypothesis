module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LemmaLSeriesWeightsOfGreenCuspidalParametrisatio
public import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

@[expose] public section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admLq_of_green_of_eSerTie : Green → ∀ D : Formalism.BasicNotions.D7, ESerTie D → admLq D := by
  first | exact @GlobalTheory.GLq.lemmaL_series_weights_of_greenCuspidalParametrisation | exact GlobalTheory.GLq.lemmaL_series_weights_of_greenCuspidalParametrisation | (intros; apply GlobalTheory.GLq.lemmaL_series_weights_of_greenCuspidalParametrisation <;> assumption)
