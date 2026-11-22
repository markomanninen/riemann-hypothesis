module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.HookBoundOfSteps
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.ProdFactorialLe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.DeterminantAdjugate
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.HighestWeightLastZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.DetShift
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.HookNorm

@[expose] public section

namespace PI.HookSteps

theorem hookBound_of (hD : DetDetId) : PI.HookBound :=
  hookBound_of_steps hook_bound hook_norm determinant_shift_norm rename_isomorphism
    highest_weight_det_mul highest_weight_last_zero determinant_adjugate hD polynomial_eq_divisibility

end PI.HookSteps
