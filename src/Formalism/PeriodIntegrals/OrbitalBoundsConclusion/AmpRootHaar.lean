module

public import Formalism.PeriodIntegrals.AmpRootH
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupHaar.RootHaarMain

@[expose] public section

theorem amplifier_root_haar : PI.AmpRootH.RootHaar := PI.AmpRootHaarW.rootHaar_main
