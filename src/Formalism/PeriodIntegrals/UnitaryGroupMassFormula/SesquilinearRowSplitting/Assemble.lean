module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.SplitRowOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.CoreStepOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.FrameReduction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.SecondDualReduction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.AdjointActionReduction

@[expose] public section

namespace PI.SRW

theorem splitRow_of_iso (hi : IsoStep) : PI.SplitRow.SplitRow :=
  splitRow_of (coreStep_of frame_reduction hi assembly_reduction) adjoint_action_reduction trace_reduction

end PI.SRW
