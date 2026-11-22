module

public import Formalism.PeriodIntegrals.LocFramePrim
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalPrimitiveFrame.StepsTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalPrimitiveFrame.DiffLoc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalPrimitiveFrame.DualFunctionalsExist
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalPrimitiveFrame.Assemble

@[expose] public section

theorem locFramePrim : PI.LocFramePrim.Statement :=
  PI.LocFramePrimWork.Steps_top PI.LocFramePrimWork.localDifferentPowerSpan PI.LocFramePrimWork.dualFunctionalsExist
    PI.LocFramePrimWork.primitiveOfDualFunctionals
