module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.TraceOneUnramified
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowUnitCondition

@[expose] public section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

theorem row_class_holds : RowClass := rowClass_of_zunit row_unit_condition

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
