module

public import Mathlib
public import Formalism.PeriodIntegrals.AdBridgeSteps
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RealFieldComparison.JmMulApply

@[expose] public section

theorem adelic_compact_real_places : PI.AdBridgeSteps.RealK := PI.UnitaryGroupMassFormula.BridgeRealK.realK
