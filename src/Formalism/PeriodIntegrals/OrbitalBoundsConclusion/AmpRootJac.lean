module

public import Formalism.PeriodIntegrals.AmpRoot
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupJacobian.ContinuousRootCoords

@[expose] public section

theorem amplifier_root_jacobian : PI.AmpRoot.RootJac := PI.AmpRootJacW.rootJac
