module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchIntDecompose
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PBranchChartIntX
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.ParametrisationSheetsConnectedHolds
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericProjectionFinite
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionsContainOpen
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsFinite
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjHomInjective
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsOpen
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsExists
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLeadIdealDim
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLinearFormCut
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHomogDimZeroPow
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PUnitaryZariskiDense
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchProperAtPointHoldsStatement

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar

theorem branchIntDecompose : GroundTheory.Heights₂.Heights.BranchIntDecompose.Statement :=
  GroundTheory.Heights₂.Heights.BranchIntDecompose.proof GlobalTheory.T.branch_proper_at_point_holds
    (GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.proof
      (GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsContainOpen.proof
        GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsFinite.proof
        GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjHomInjective.proof
        GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsOpen.proof
        (GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsExists.proof
          GroundTheory.Heights₂.Heights.ComplexSets.LeadIdealDim.proof
          GroundTheory.Heights₂.Heights.ComplexSets.LinearFormCut.proof
          GroundTheory.Heights₂.Heights.ComplexSets.HomogDimZeroPow.proof))
      GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense.proof)
    GroundTheory.Heights₂.Heights.AutoClose.ChartIntSumOffHyperplane
    GroundTheory.Heights₂.Heights.Swarm.BranchChartInt.proof

end GlobalTheory.CompanionTheory.Ar
