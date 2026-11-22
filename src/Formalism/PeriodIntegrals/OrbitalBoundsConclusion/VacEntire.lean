module

public import Mathlib
public import Formalism.PeriodIntegrals.VacEntire
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.VacuumEntire.AnalyticAtHfLeft

@[expose] public section

theorem entireStatements_holds : PI.VacEntire.Target :=
  ⟨PI.VacEntire.UnitaryGroupMassFormula.iopEntire, PI.VacEntire.UnitaryGroupMassFormula.tensEntire⟩
