module

public import Mathlib
public import Formalism.PeriodIntegrals.FglGram
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramUnitMultiplication.BeMulByZero

@[expose] public section

theorem gramExpansion_orthonormal : PI.FglGram.GramUnit := PI.UnitaryGroupMassFormula.GramUnit.gramUnit
