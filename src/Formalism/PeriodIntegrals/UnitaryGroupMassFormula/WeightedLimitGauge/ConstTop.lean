module

public import Mathlib
public import Formalism.PeriodIntegrals.RhsWLim
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstCut
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstPair
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsTest
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.TransW
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.PolarHyp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.PolarDec

@[expose] public section

noncomputable section

namespace PI.RhsWLim.W

open PI.RhsWLim

theorem constVal_of_unimodW_orbitPush (hU : UnimodW) (hO : OrbitPush) : ConstVal :=
  constVal_of_polarHyp rhsTest transW hU hO polarHyp

theorem constVal_of_orbit (hO : OrbitPush) : ConstVal :=
  constVal_of_unimodW_orbitPush unimodW hO

end PI.RhsWLim.W
