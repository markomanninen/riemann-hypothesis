module

public import Mathlib
public import Formalism.PeriodIntegrals.MirabIndex
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicIndex.RowMulOfMirab

@[expose] public section

theorem mirabolic_index : PI.MirabIndex.MirabIndex := PI.MirabolicIndex₂.mirabIndex
