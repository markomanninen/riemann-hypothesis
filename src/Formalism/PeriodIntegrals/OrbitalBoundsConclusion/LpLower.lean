module

public import Mathlib
public import Formalism.PeriodIntegrals.LpLower
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LinearProgramLowerBound.LpFeasibleLe

@[expose] public section

theorem lp_lower_bound : PI.LpLower := PI.lpLower_main
