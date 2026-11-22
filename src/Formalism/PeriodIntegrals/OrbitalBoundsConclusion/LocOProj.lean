module

public import Mathlib
public import Formalism.PeriodIntegrals.LocHerm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalOrderProjection.LocOProjOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalOrderProjection.ProjOfFreeIdem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalOrderProjection.IsFieldOfNonsq

@[expose] public section

theorem projectiveOverOrder : PI.LocHerm.LocOProj :=
  PI.LocHerm.OProj.locOProj_of PI.LocHerm.OProj.sqCase PI.LocHerm.OProj.nonSqCase
