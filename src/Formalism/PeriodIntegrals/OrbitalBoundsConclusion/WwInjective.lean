module

public import Mathlib
public import Formalism.PeriodIntegrals.WwInjective
public import Formalism.PeriodIntegrals.WwCauchyBinet
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramInjectivity.InstFintypeColChoice

@[expose] public section

theorem wwInjective_of (h : PI.WwCauchyBinet.WwCauchyBinet) : PI.WwInjective.WwInjective :=
  PI.WwInjectiveWork.wwInjective_of h
