module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceBranchInt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamChartInt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChartIntCountAdd
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamPieceInt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamCritNull
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamOffRegularZero
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularInjectivePieces
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamDensIntegrable
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchProperAtPointHoldsStatement

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.SliceBranch

theorem paramChartInt : GroundTheory.Heights₂.Heights.ParamChartInt.Statement :=
  GroundTheory.Heights₂.Heights.ParamChartInt.proof
    (GroundTheory.Heights₂.Heights.ChartIntCountAdd.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact)
    GroundTheory.Heights₂.Heights.ParamPieceInt.proof GroundTheory.Heights₂.Heights.ParamCritNull.proof
    GroundTheory.Heights₂.Heights.ParamOffRegularZero.proof GroundTheory.Heights₂.Heights.RegularInjectivePieces.proof
    GroundTheory.Heights₂.Heights.ParamDensIntegrable.proof

theorem sliceBranchInt : GroundTheory.Heights₂.Heights.SliceBranchInt.Statement :=
  GroundTheory.Heights₂.Heights.SliceBranchInt.proof GlobalTheory.T.branch_proper_at_point_holds paramChartInt

end GlobalTheory.CompanionTheory.Ar.SliceBranch
