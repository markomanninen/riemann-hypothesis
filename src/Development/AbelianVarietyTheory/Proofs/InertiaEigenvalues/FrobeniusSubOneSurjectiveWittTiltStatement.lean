module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Formalism.PeriodIntegrals.ArtSch
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ASWitt
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ASRoot
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TiltDivisibility
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ASSmall
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ASGlue

@[expose] public section

theorem _root_.GlobalTheory.T.frobenius_sub_one_surjective_witt_tilt : Formalism.MainNotions.ElementDenominator.ArtinSchreierWittOnto := fun l _ x =>
  PI.ArtSch.main_of witt_lift (tiltSurjectiveOfParts rootModP_holds tilt_divisibility smallSurjective) l x
