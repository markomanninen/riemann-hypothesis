module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.PurCauchy
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.BlockDegreeAntitone

@[expose] public section

namespace PI.FJMB

theorem cauchy_highest_weight_of_shape (hS : HypShape) (hD : HypDiag) (hF : HypFree) : PI.FJM.CauchyHW := by
  refine cauchyHW_of ?_ hS hD hF
  intro σ m n ι hι α P hP hrow hdeg
  exact PI.FJMF.block_degree_antitone σ m n ι hι α P hP hrow hdeg

end PI.FJMB
