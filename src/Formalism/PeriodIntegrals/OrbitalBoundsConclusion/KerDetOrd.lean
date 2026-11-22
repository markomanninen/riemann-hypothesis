module

public import Mathlib
public import Formalism.PeriodIntegrals.KerIso
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DeterminantKernelOrder.ValNatCastEqOne

@[expose] public section

theorem ordRelativeDet_independence : PI.KerIso.DetOrdIndep :=
  PI.KerIso.DetOrdW.detOrdIndep
