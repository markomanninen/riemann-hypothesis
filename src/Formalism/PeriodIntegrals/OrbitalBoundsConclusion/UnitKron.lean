module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitKron
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitKronecker.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitKronecker.PosDefFormNeZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitKronecker.EqZeroOfMulVec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitKronecker.IntRootProp

@[expose] public section

theorem unit_kronecker : PI.UnitKron :=
  PI.UnitKronW.unitKron_of PI.UnitKronW.stepA PI.UnitKronW.stepB PI.UnitKronW.stepC
