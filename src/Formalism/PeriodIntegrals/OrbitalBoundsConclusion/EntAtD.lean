module

public import Mathlib
public import Formalism.PeriodIntegrals.EntAtD
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.EntAtDOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.ExpCoeff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.Bridge
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.LapComm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.MinorAff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.SDegMul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.LapForms

@[expose] public section

theorem jet_bound_ramified_prime : PI.EntAtD.EntAtD :=
  PI.EntAtD.W.entAtD_of PI.EntAtD.W.pExpCoeff PI.EntAtD.W.pBridge PI.EntAtD.W.pLapComm
    PI.EntAtD.W.pMinorAff PI.EntAtD.W.pSDegMul PI.EntAtD.W.pLapForms
