module

public import Mathlib
public import Formalism.PeriodIntegrals.OkpInert
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.OkpInertMain

@[expose] public section

theorem integers_inert_prime : PI.OkpInert := PI.OkpW.okpInert_main
