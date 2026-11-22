module

public import Mathlib
public import Formalism.PeriodIntegrals.SelfDualLoc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.SelfDualLocOfLocBasis
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.LocBasis

@[expose] public section

theorem self_dual_local : PI.SelfDualLoc :=
  PI.SelfDualLoc.W.selfDualLoc_of_locBasis PI.SelfDualLoc.W.locBasis
