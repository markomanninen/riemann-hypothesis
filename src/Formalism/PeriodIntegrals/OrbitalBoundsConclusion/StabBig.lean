module

public import Mathlib
public import Formalism.PeriodIntegrals.StabBig
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LargeStabilizerInverse.GLeftInv

@[expose] public section

theorem stabilizer_large : PI.StabBig := PI.StabBigW.stabBig
