module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllOfTateDualityEulerChar
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, LocalSituation.Conclusion5 D := by
  first | exact @GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂.aux_of_blochKato_tateDuality_eulerChar₂ | exact GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂.aux_of_blochKato_tateDuality_eulerChar₂ | (intros; apply GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂.aux_of_blochKato_tateDuality_eulerChar₂ <;> assumption)
