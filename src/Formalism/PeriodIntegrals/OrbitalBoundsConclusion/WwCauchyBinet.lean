module

public import Mathlib
public import Formalism.PeriodIntegrals.WwCauchyBinet
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CauchyBinet.WwCauchyBinetMain

@[expose] public section

theorem cauchy_binet_minors : PI.WwCauchyBinet.WwCauchyBinet := PI.WwCauchyBinetWork.wwCauchyBinet_main
