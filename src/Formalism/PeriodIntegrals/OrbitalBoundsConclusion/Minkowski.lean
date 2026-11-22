module

public import Mathlib
public import Formalism.PeriodIntegrals.Minkowski
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.CharpolyDvdOfPowEqOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.PowerSum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.MinkowskiBoundOfSteps

@[expose] public section

theorem card_dvd_minkowskiNumber : PI.MinkowskiBound :=
  PI.Mk.minkowskiBound_of_steps PI.Mk.traceStep PI.Mk.powerSumStep
