module

public import Mathlib
public import Formalism.PeriodIntegrals.WeilQuotMeas
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientMeasureUniqueness.WqUniqueOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientMeasureUniqueness.QLiftIsMulLeftInvariant
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientMeasureUniqueness.Weight

@[expose] public section

namespace PI

theorem wqUnique : PI.WeilQuotMeas.WqUnique :=
  PI.QuotMeasUniqW.wqUnique_of PI.QuotMeasUniqW.qmuWeight PI.QuotMeasUniqW.qmuLift

end PI
