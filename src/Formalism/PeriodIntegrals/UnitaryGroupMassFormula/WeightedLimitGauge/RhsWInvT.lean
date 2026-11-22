module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvOA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvU
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvF

@[expose] public section

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W

theorem rhsWInv_of_hypQ (hQ : HypQ) : RhsWInv := rhsWInv_of_hyp hQ unimodK fibTrans

end PI.RhsWLim.W.RI
