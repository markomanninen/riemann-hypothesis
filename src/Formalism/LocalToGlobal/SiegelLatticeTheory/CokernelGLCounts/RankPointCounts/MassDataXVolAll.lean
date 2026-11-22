module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataVolumesS
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataLevelS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXMasses
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXColumns
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXRed

@[expose] public section

namespace Formalism.L2.SG.Pf.MassDataX

theorem massDataVolAll_of (hSW : PI.VolStabS.MassDataS.SWXS) :
    Formalism.L2.SG.PoincareAmplitudeLowerBounds.MassDataVolAll := by
  intro D T u u' X0 sd C Th Q i0 i0' νq
  refine ⟨PI.VolStabS.MassDataS.inVolumesAt_of_SWS hSW _ _ _ _ _ _ _ _ _ _, ?_, ?_, ?_, ?_⟩
  · first
      | apply level_s_at_instance
      | apply PI.Final.level_s_at_instance
      | apply PI.level_s_at_instance
      | apply MassDataLevelSSteps.inLevelSAt_holds
      | apply PI.MassDataLevelSSteps.inLevelSAt_holds
      | apply PI.UnitaryGroupMassFormula.MassDataLevelSSteps.inLevelSAt_holds
  · apply inMassesAt_holds
  · apply inColumnsAt_holds
  · apply inIndicesAt_holds

end Formalism.L2.SG.Pf.MassDataX
