module

public import Mathlib
public import Formalism.PeriodIntegrals.GZeroLogBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GeneralLinearCardBound.ZeroLogBound

@[expose] public section

theorem GZeroLogBound : PI.GZeroLogBound.Target := PI.GZeroLogBound.UnitaryGroupMassFormula.target
