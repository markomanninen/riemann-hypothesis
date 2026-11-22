module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchProperAtPointHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchIntDecompose
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceBranchInt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimitAtBranches
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitAtBranches
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPolydiscLelongLimit

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Lelong

open GroundTheory.Heights₂.Heights

theorem lelongLimitAtBranches : LelongLimitAtBranches.Statement :=
  LelongLimitAtBranches.proof GlobalTheory.CompanionTheory.Ar.branchIntDecompose GlobalTheory.CompanionTheory.Ar.SliceBranch.sliceBranchInt
    PolydiscLelongLimit.proof GlobalTheory.CompanionTheory.Ar.Branch.branchProperAtPoint

end GlobalTheory.CompanionTheory.Ar.Lelong
