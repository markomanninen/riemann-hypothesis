module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauchyHighestWeightOfShape
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.DiagonalImageBlockFree

@[expose] public section

namespace PI.FJMB

theorem cauchyHW_of_shape (hS : HypShape) : PI.FJM.CauchyHW :=
  cauchy_highest_weight_of_shape hS diagonal_hypothesis diagonal_image_block_free

end PI.FJMB
