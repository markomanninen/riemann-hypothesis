module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.PhNormOfUnits
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CubeOfTwoIdentities
public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CubeFormalIdentities.CoeffPowMulPowEqZero
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhNormUnits
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhNormLimit

@[expose] public section

namespace Formalism.MainNotions.Ext.CutA

theorem phNormOfUnits_holds : PhNormOfUnits := by
  intro p _ g S hok
  exact phase_norm_units p g.l g.ex g.ph S hok.2.2.1 hok.2.2.2

theorem phNormClosed_holds : PhNormClosed := by
  intro p _ g S hok
  exact phase_norm_limit_target p g.l g.ex g.ph S hok.2.2.1 hok.2.2.2

end Formalism.MainNotions.Ext.CutA
