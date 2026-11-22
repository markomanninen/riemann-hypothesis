module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.InjectiveHolomorphicJacobianNeZeroHolds
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.BranchInverseOffHypersurfaceHolds
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.RegularLocusIdentityHolds
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalDimDomain
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceBundleRadicalAway
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceMultGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceReducedAwayZariski
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceUnmixedGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTransverseSliceGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceReducedAway
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceReducedGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLength
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalOrder
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceBranchesHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CurveBranchLengthHoldsStatement

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Heights.BranchOrder

open GroundTheory.Heights₂.Heights

theorem sliceReducedAwayZariski : SliceReducedAwayZariski.Statement :=
  @SliceReducedAwayZariski.proof AutoClose.GenericFibreRadicalAway SliceBundleRadicalAway.proof

theorem sliceReducedAway : SliceReducedAway.Statement :=
  @SliceReducedAway.proof sliceReducedAwayZariski

theorem sliceUnmixedGeneral : SliceUnmixedGeneral.Statement :=
  @SliceUnmixedGeneral.proof AutoClose.CMHeightOneGeneral LocalDimDomain.proof
    AutoClose.SliceLocalDimGeneral AutoClose.SliceCMUnmixed

theorem sliceReducedGeneral : SliceReducedGeneral.Statement :=
  @SliceReducedGeneral.proof sliceUnmixedGeneral sliceReducedAway

theorem sliceMultGeneral : SliceMultGeneral.Statement :=
  @SliceMultGeneral.proof AutoClose.CMGeneralPoint TransverseSliceGeneral.proof AutoClose.LengthTransverseSlice

theorem sliceLength : SliceLength.Statement :=
  @SliceLength.proof IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.full sliceReducedGeneral sliceMultGeneral

theorem localOrder : LocalOrder.Statement :=
  LocalOrder.proof sliceLength GlobalTheory.T.slice_branches_holds GlobalTheory.T.curve_branch_length_holds

end GlobalTheory.CompanionTheory.Heights.BranchOrder
