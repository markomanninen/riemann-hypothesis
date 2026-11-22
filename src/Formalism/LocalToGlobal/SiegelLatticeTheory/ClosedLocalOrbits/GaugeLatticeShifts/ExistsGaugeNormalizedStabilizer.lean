module

public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ExistsGaugeNormalizedStabilizer
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstGEB

@[expose] public section

namespace Formalism.L2.SG.Pf.GE

theorem existsGaugeNormalizedStabilizer : ExistsGaugeMeasureForEachRank := (show PI.ExistsGaugeMeasureForEachRank.ExistsGaugeMeasureForEachRank ↔ ExistsGaugeMeasureForEachRank from Iff.rfl).mp _root_.exists_gaugeNormalizedStabilizer

end Formalism.L2.SG.Pf.GE
