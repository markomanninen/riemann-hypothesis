module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.PurCauchy
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.LeadTDerCols

@[expose] public section

namespace PI.FJMX

theorem minorProductDiagonal : PI.FJMB.HypShape := fun _ _ ι hι α hα =>
  ⟨shapeProd_hwb ι hι _, shapeProd_diag ι hι α hα⟩

end PI.FJMX
