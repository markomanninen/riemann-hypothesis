module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowSurjOfGenus
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.UnimodularOneGenus

@[expose] public section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

theorem row_surjective : RowSurj := rowSurj_of_genus PI.UnitaryGroupMassFormula.CntFormula.UG.unimodular_one_genus

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
