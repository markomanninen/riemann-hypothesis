module

public import Mathlib
public import Formalism.PeriodIntegrals.LongWeylElementSquare
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BigCellConjugation.Monomial

@[expose] public section

theorem big_cell_g : PI.SwBig.BigCellG := PI.SwBig.BigCellGProof.bigCellG
