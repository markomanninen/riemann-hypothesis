module

public import Mathlib
public import Formalism.PeriodIntegrals.Transference
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Skeleton
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Poisson
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.NumericMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.KeySmall

@[expose] public section

theorem transference_covering : PI.TransferenceCover :=
  PI.Tr.transferenceCover_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall
