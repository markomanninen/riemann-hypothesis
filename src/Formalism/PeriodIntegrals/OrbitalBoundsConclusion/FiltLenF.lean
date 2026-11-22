module

public import Mathlib
public import Formalism.PeriodIntegrals.FiltLenF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiltrationLength.FiltLenFMain

@[expose] public section

theorem filtration_length_bound : PI.FiltLenF := PI.FiltrationLength.filtLenF_main
