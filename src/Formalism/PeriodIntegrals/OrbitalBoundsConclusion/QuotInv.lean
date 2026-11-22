module

public import Mathlib
public import Formalism.PeriodIntegrals.QuotInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientInvariantMeasurability.MeasurableAvgS

@[expose] public section

theorem quotient_invariant : PI.QuotInv := PI.QuotInvW.quotInv
