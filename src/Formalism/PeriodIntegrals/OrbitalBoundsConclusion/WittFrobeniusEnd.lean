module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittEndomorphism.WfEndOfLog
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittLogarithm

@[expose] public section

theorem witt_pairing : PI.PairW := PI.WfEndProof.pairW

theorem witt_frobenius_end : PI.WfEnd := PI.WfEndProof.wfEnd_of_log witt_logarithm

theorem wfEnd_of : PI.WfRing → PI.WfSubst → PI.WfLog → PI.WfEnd := PI.WfEndProof.wfEnd_of
