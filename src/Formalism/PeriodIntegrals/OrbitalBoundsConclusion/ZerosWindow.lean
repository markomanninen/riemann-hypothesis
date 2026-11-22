module

public import Mathlib
public import Formalism.PeriodIntegrals.ZerosWindow
public import Formalism.PeriodIntegrals.ZerosWindowIn
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.Transfer

@[expose] public section

theorem zerosWindow_of : PI.LBoundRight → PI.ZetaBoundRight → PI.LInvRight → PI.ZerosWindow :=
  fun hL hZ hI => PI.ZW.zerosWindow_of_transfer PI.ZW.transfer hL hZ hI
