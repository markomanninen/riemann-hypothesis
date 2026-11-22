module

public import Mathlib
public import Formalism.PeriodIntegrals.ScMuExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.TargetOfInstDecomp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstAll

@[expose] public section

namespace PI

theorem sc_mu_exists : PI.ScMuExists.Target :=
  PI.ScMuExists.UnitaryGroupMassFormula.target_of_instDecomp PI.ScMuExists.UnitaryGroupMassFormula.place_decomposition_instance

end PI
