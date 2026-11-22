module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHsymmPairFlagIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSymmetricSpanHsymm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExist
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDvrConeDimTrdeg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairBundleTrdeg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PAdjoinTrdegAdd
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairConeLinesIndep
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairConeAlg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExpress
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreClosureNumber
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureTrdeg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagConeAlg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosurePullback
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberRelabel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVerticalDivisorJoinPullback
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureBirational
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.VerticalDivisorsCommuteStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PairNumberPullbackStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHeckeCorrespondenceOnIntegralShimuraModelStatement

@[expose] public section

namespace PositivityTheory.Xgn.A_s_flagindep

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem closureModel : GenericProjClosureModel.Statement :=
  GenericProjClosureModel.proof TwistedDualGensExist.proof
    (GenericProjClosureDim.proof DvrConeDimTrdeg.proof
      (PairBundleTrdeg.proof AdjoinTrdegAdd.proof PairConeLinesIndep.proof PairConeAlg.proof))
    (GenericProjClosureDivisor.proof TwistedDualGensExpress.proof)

theorem flagClosureModel : SegreFlagClosureModel.Statement :=
  SegreFlagClosureModel.proof (SegreFlagClosureTrdeg.proof SegreFlagConeAlg.proof)

theorem of_items (hC2 : VerticalDivisorsCommute.Statement.{0}) (hPull : PairNumberPullback.Statement)
    (hCut : SegreFlagClosureCut.Statement) : FlagIndependence.Statement := by
  have hPE := PairNumberExpansionIndependence.proof hC2
  have hSP := SegreFlagClosurePullback.proof hPull hPE flagClosureModel PairNumberRelabel.proof
    VerticalDivisorJoinPullback.proof SegreFlagClosureBirational.proof
  have hSCN := SegreClosureNumber.proof hPE flagClosureModel hCut hSP
  exact FlagIndependence.proof hPE (HsymmPairFlagIndependence.proof hPE closureModel hSCN)
    SymmetricSpanHsymm.proof

end PositivityTheory.Xgn.A_s_flagindep
