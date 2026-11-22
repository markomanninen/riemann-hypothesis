module

public import Mathlib
public import Formalism.PeriodIntegrals.AddIntG
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.AddIntGTop

@[expose] public section

theorem additive_integral_generation : PI.AddIntG.Target := PI.AddIntG.Wk.addIntG_top
