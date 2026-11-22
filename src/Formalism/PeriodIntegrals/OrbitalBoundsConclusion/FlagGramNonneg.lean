module

public import Mathlib
public import Formalism.PeriodIntegrals.FlagGramNonneg
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagGramNonnegativity.Gval

@[expose] public section

theorem flag_gram_nonneg : PI.FlagGramNonneg := PI.UnitaryGroupMassFormula.FlagGramNonneg.main
