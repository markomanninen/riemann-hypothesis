module

public import Mathlib
public import Formalism.PeriodIntegrals.HookBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.CapelliOps

@[expose] public section

theorem hook_length_bound : PI.HookBound := PI.HookSteps.hookBound_of PI.HookSteps.Cap.capelli_determinant_identity
