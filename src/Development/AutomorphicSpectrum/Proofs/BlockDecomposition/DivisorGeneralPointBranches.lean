module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsAbsIntegrable
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorGeneralPointBranches
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimitAtBranches
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegMassNearSmall
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorGeneralPointBranches
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorBranches
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorOneComponent
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelExists
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalDivisorChartGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelDivisorChartGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelGoodPointGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelGoodPointChart
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalCodimOneCompleteIntersection
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalCodimOneUniformiser
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PJacobianRankOffHypersurface
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProjectionUnramifiedGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalDoublePointsGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorGoodPointBranches
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.BranchInverseOffHypersurfaceHolds

@[expose] public section

namespace GlobalTheory.CompanionTheory.ComplexSets


open GroundTheory.Heights₂.Heights in
theorem divisorGeneralPointBranches : GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches.Statement :=
  DivisorGeneralPointBranches.proof DivisorOneComponent.proof
    (DivisorBranches.proof IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof
      GroundTheory.Heights₂.Heights.AutoClose.DivisorRegularGeneric
      (NormalDivisorChartGeneric.proof
        (NormalModelDivisorChartGeneric.proof
          (NormalModelGoodPointGeneric.proof NormalCodimOneCompleteIntersection.proof
            NormalCodimOneUniformiser.proof JacobianRankOffHypersurface.proof
            ProjectionUnramifiedGeneric.proof)
          NormalModelGoodPointChart.proof))
      NormalDoublePointsGeneric.proof DivisorGoodPointBranches.proof)

end GlobalTheory.CompanionTheory.ComplexSets
