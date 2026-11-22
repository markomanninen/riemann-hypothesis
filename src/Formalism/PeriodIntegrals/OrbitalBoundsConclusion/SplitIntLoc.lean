module

public import Mathlib
public import Formalism.PeriodIntegrals.SplitIntLoc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitPrimeIntegers.ExistsUnitDiff

@[expose] public section

theorem split_integral_local : PI.SplitIntLoc := PI.SplitIntLoc.Proof.main
