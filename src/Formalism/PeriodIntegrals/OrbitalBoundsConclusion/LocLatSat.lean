module

public import Mathlib
public import Formalism.PeriodIntegrals.LocLatSat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeSaturation.LocLatSat

@[expose] public section

theorem inf_eq_inter_span : PI.LocLatSat.Stmt := PI.LocLatSat.UnitaryGroupMassFormula.locLatSat
