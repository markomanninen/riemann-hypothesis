module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.ThetaDerivNe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.ThetaA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.ThetaNz
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.Reduce
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.GenEqOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.LatExt

@[expose] public section

namespace PI.SSE

theorem sigmaStarEx : PI.SigmaStarEx :=
  sigmaStarEx_of_parts thetaA thetaDerivNe reduceBasis genEqOf latExt

end PI.SSE
