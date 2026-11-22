module

public import Mathlib
public import Formalism.PeriodIntegrals.LocDualGen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.LocDualGenOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.UnramifiedDualGenerator

@[expose] public section

theorem local_dual_generation : PI.LocDualGen.Stmt :=
  PI.LocDualGen.Of.locDualGen_of PI.LocDualGen.FpU.unramified_dual_generator
