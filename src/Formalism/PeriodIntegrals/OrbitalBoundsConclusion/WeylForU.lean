module

public import Mathlib
public import Formalism.PeriodIntegrals.WeylForU
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaUnitary.NatWCastReal

@[expose] public section

theorem weylForU_of : PI.ModelIso → PI.NablaDim → PI.WeylForU := PI.WeylForUWork.weylForU_of
