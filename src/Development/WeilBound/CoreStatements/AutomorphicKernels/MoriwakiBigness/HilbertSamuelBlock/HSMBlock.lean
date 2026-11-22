module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyConditional
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBridge
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionDegree
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFSMass
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegGeomDeg
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionDegreeIntegral
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHSMTransport
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKrullDimMatAct
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameGraphDeg
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGraphChangeOfModel
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockGraphDeg
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseGraphDeg
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseGramMono
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockPieceIndex
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockModuleFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PModulePieceHilbert
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockModuleCycle
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionImageSup
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageInverse
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIsomInvariance
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGraphIsometric
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ChangeOfModel
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAbsIntegrable
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAbsMeasurable
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GraphStatementHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreDim
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfArithSystemStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatementStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatementStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeAndCoordinatesOfResolutionStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem

@[expose] public section

namespace PositivityTheory.LocalParametersCuspidal.MB.HSM

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4
  ReciprocityTheory.ChartRestriction.G.AI.I1

theorem theoremHSMBlock (hAIS : ArithIntersectionSystemStatement) (hResK : ResK.ResKStatement) :
    TheoremHSMBlock.Statement := by
  have hGr : GraphStatement := GlobalTheory.T.graph_statement_holds
  have hAI3 : Inter.PushforwardArithIntersection.Statement := GlobalTheory.T.generic_degree_of_arith_system hAIS
  have hRes : ResExistsStatement := GlobalTheory.T.resolution_exists_of_resolution_statement hResK
  have hPts : PtsIntegrableStatement := GlobalTheory.T.points_integrable_of_resolution_statement hResK
  have hPF : PFCoordStatement := (GlobalTheory.T.degree_and_coordinates_of_resolution hRes).2
  have hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι := Targets.existsUniqueAll
  have hGF : GenFibreExistsStatement := Targets.genFibreExists
  have hIso : IsomInvariance.Statement := IsomInvariance.proof (Inter.RatR.proof hPts)
  have hCM : ChangeOfModelStatement :=
    Targets.ChangeOfModel.of_found hAI3 hGr hIso GraphIsometric.proof
  have hDim : FibreDimStatement := GlobalTheory.CompanionTheory.Ar.Giv.fibreDim
  have hDG : Inter.DegreeGeneric.Statement :=
    GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system hAIS)
  have hAbs : Inter.PtsAbsIntegrable.Statement :=
    Inter.PtsAbsIntegrable.proof hPts (Inter.PtsAbsMeasurable.proof hRes)
  have h6 : ProjFrameGraphDeg.Statement :=
    ProjFrameGraphDeg.proof hEU ProjFrameFibrePt.full ProjFrameFibreDeg.full
  have h15 : GraphChangeOfModel.Statement :=
    GraphChangeOfModel.proof hAI3 hGr hGF hEU hIso GraphIsometricForms.full
  have h16 : BlockGraphDeg.Statement :=
    BlockGraphDeg.proof hGr BlockGraphImage.full hGF hDim hEU Closed.Inter.ChartRankAdjoin
      BlockGraphFibreRatio.full
  have h18 : VeroneseGraphDeg.Statement :=
    VeroneseGraphDeg.proof hGr VeroneseGraphImage.full hDim hEU
  exact TheoremHSMBlock.of_open TwoBlockPieceIndex.proof TwoBlockModuleFinite.proof
    ModulePieceHilbert.proof TwoBlockModuleCycle.proof hPF hCM h6
    (HSMTransport.proof KrullDimMatAct.proof)
    (ResolutionDegree.proof PullFSExtension.full ProjFSMass.proof) ResolutionMixedBridge.full
    (BlockResolutionImageSup.proof ChartSupBound.full)
    (BlockResolutionDegreeIntegral.proof (GenDegGeomDeg.proof hDG)) BlockResolutionMixedBridge.full
    hAbs BlockImageInverse.proof h15 h16 VeroneseGramMono.proof h18

end PositivityTheory.LocalParametersCuspidal.MB.HSM
