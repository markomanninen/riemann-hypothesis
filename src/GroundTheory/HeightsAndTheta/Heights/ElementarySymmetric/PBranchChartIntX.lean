module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchChartInt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchSheetAE
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicFibreSumInt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PWeightedAreaFormula
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRankDeficientFibreInfinite
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFibreBound
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantCover
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantSheetCover
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveElementFibres

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Swarm

theorem BranchChartInt.proof : GroundTheory.Heights₂.Heights.BranchChartInt.Statement :=
  GroundTheory.Heights₂.Heights.BranchChartInt.proof
    (GroundTheory.Heights₂.Heights.HolomorphicFibreSumInt.proof GroundTheory.Heights₂.Heights.WeightedAreaFormula.proof)
    (GroundTheory.Heights₂.Heights.BranchSheetAE.proof
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RankDeficientFibreInfinite.proof
      GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.proof
      (GroundTheory.Heights₂.Heights.DiscriminantSheetCover.proof
        (GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.proof
          GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveElementFibres.proof)))
    GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.proof

end GroundTheory.Heights₂.Heights.Swarm
