module

public import Mathlib
public import Formalism.PeriodIntegrals.WwMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LFunctionMinors.InfinitePadicComplex
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LFunctionMinors.LfunEqOfSubset
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LFunctionMinors.SumInjEqSumPairs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LFunctionMinors.DeXCBOf

@[expose] public section

theorem minor_identity : PI.WwMain.WwMain :=
  PI.WwMainW.wwMain_of PI.WwMainW.evalH PI.WwMainW.lH PI.WwMainW.lLin
    (PI.WwMainW.deXCB_of PI.WwMainW.cbSorted)
