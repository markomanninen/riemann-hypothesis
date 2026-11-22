module

public import Mathlib
public import Formalism.PeriodIntegrals.ArtSch
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittCoefficients.CoeffEqOfSubMem

@[expose] public section

theorem witt_lift : PI.ArtSch.WittLift := PI.ArtSch.WittLiftWork.wittLift
