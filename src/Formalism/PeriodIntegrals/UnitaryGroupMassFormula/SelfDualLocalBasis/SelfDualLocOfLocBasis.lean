module

public import Mathlib
public import Formalism.PeriodIntegrals.SelfDualLoc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.Assembly
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.HvecApply
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.Nondeg

@[expose] public section

noncomputable section

namespace PI.SelfDualLoc.W

theorem selfDualLoc_of_steps (hN : Nondeg) (hL : LocBasis) : PI.SelfDualLoc :=
  selfDualLoc_of sigInt hN (spanTop_of hN) hL dualBasis unitLoc

theorem selfDualLoc_of_locBasis (hL : LocBasis) : PI.SelfDualLoc :=
  selfDualLoc_of_steps nondeg hL

end PI.SelfDualLoc.W
