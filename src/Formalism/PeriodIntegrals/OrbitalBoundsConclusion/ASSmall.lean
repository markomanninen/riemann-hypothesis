module

public import Mathlib
public import Formalism.PeriodIntegrals.ArtSch
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SmallArtinSchreier.ExistsAsOfValLtOne

@[expose] public section

theorem smallSurjective : PI.ArtSch.TiltSmall := PI.UnitaryGroupMassFormula.ASSmall.tiltSmall
