module

public import Formalism.PeriodIntegrals.SzCt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.SzCtOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.FirstCoordinateLeThreeScale
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.SizeFacts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.Places

@[expose] public section

theorem sz_constant_term : PI.SzCt.SzCt :=
  PI.SzCt.UnitaryGroupMassFormula.szCt_of PI.SzCt.UnitaryGroupMassFormula.rowA PI.SzCt.UnitaryGroupMassFormula.rowB PI.SzCt.UnitaryGroupMassFormula.rowC
    PI.SzCt.UnitaryGroupMassFormula.sizeFacts PI.SzCt.UnitaryGroupMassFormula.placeFacts
