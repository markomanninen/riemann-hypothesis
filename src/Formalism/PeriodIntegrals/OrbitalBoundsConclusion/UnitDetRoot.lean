module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitDetRoot
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.Partial
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobFin

@[expose] public section

theorem unit_det_root_of_unity : PI.UnitDetRoot :=
  PI.UnitaryGroupMassFormula.UnitDetRoot.unitDetRoot_of_global PI.UnitaryGroupMassFormula.UnitDetRoot.globalLUnit
