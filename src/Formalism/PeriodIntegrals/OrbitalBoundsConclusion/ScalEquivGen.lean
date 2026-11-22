module

public import Mathlib
public import Formalism.PeriodIntegrals.ScalPairs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarEquivalenceGeneral.ScalarFactorEqOneOfLe

@[expose] public section

theorem scalar_equiv_general : PI.ScalPairs.ScalarEquivG :=
  PI.UnitaryGroupMassFormula.ScalEquivGen.scalarEquivG_holds
