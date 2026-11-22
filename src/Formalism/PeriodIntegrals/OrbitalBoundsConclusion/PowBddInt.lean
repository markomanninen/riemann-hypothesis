module

public import Mathlib
public import Formalism.PeriodIntegrals.PowBddInt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerBoundedIntegrality.Imports
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerBoundedIntegrality.EvalIntMapEqZero

@[expose] public section

theorem power_bounded_integral : PI.PowBddInt :=
  PI.PowBddIntWork.powBddInt_of PI.PowBddIntWork.stepA PI.PowBddIntWork.stepB
