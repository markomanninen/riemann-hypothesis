module

public import Mathlib
public import Formalism.PeriodIntegrals.KerIso
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DeterminantKernelFiniteness.ExistsDenomBackward

@[expose] public section

theorem ordRelativeDet_finite : PI.KerIso.DetOrdFin := PI.KerDetFinW.detOrdFin
