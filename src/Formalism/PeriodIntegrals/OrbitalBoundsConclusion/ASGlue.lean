module

public import Mathlib
public import Formalism.PeriodIntegrals.ArtSch
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationGluing.ValbLeOfCoeffEqZero

@[expose] public section

theorem tiltSurjectiveOfParts : PI.ArtSch.TiltGlue := PI.ArtSch.Glue.tiltGlue
