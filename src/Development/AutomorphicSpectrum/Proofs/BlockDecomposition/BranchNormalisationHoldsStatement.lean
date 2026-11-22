module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchNormalisationHolds
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
theorem _root_.GlobalTheory.T.branch_normalisation_holds : GroundTheory.Heights₂.Heights.BranchNormalisation.Statement := by
  first | exact @GlobalTheory.CompanionTheory.BranchNorm.branchNormalisation | exact GlobalTheory.CompanionTheory.BranchNorm.branchNormalisation | (intros; apply GlobalTheory.CompanionTheory.BranchNorm.branchNormalisation <;> assumption)
