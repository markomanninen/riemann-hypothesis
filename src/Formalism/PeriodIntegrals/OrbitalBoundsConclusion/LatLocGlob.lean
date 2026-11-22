module

public import Formalism.PeriodIntegrals.LatLocGlob
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGlobalLattice.ExistsSmulMemOfLocal

@[expose] public section

theorem latLocGlob : PI.LatLocGlob.LatLocGlob := PI.LatLocGlob.Proof.latLocGlob_core
