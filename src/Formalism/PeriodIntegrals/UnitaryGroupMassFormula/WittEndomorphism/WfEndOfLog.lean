module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittEndomorphism.FlogConstantCoeff
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WfRing
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WfSubst

@[expose] public section

namespace PI.WfEndProof

theorem wfEnd_of_log (hL : WfLog) : WfEnd := wfEnd_of witt_ring_structure witt_substitution hL

end PI.WfEndProof
