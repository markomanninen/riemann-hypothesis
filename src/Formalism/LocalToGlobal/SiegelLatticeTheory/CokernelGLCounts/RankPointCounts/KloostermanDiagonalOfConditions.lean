module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KloostermanTermANonneg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KloostermanCosetSumLe
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ExpQuarterMulExpQuarterLeTwo
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KppOffCOfSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramLocPfB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GrowthOfBasic
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryDimensionFormula

@[expose] public section

noncomputable section

open Formalism.L2.SG.Full Formalism.L2.SG.KappaOffDiagonal

namespace Formalism.L2.SG.KappaOffDiagonal

theorem corankPosC_holds : Formalism.L2.SG.RowsConc.CorankPosC :=
  fun _ _ Y u u' _ => Formalism.L2.SG.Pf.SatGram.corankPos_tO Y u u'

end Formalism.L2.SG.KappaOffDiagonal
