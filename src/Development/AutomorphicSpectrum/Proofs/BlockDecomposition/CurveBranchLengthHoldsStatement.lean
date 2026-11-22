module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CurveBranchLengthHolds
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchProperAtPoint
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchIntDecompose
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBranchInt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBranches
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveBranchLength
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchNormalisation
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegBallMass
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegLelongMono
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSmallSetBallCover

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_branch_length_holds : GroundTheory.Heights₂.Heights.CurveBranchLength.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Heights.CurveBranch.curveBranchLength | exact GlobalTheory.CompanionTheory.Heights.CurveBranch.curveBranchLength | (intros; apply GlobalTheory.CompanionTheory.Heights.CurveBranch.curveBranchLength <;> assumption)
