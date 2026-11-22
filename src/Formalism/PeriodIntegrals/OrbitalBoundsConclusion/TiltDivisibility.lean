module

public import Mathlib
public import Formalism.PeriodIntegrals.ArtSch
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TiltedDivisibility.TiltDivOfGeneral

@[expose] public section

theorem tilt_divisibility : PI.ArtSch.TiltDiv := PI.ArtSch.tiltDiv_of_general
