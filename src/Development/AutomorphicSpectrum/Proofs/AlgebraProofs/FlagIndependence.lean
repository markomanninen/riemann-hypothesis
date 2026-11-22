module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSFlagindep
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.VerticalDivisorsCommute
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PairNumberPullbackStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHeckeCorrespondenceOnIntegralShimuraModelStatement

@[expose] public section

namespace GlobalTheory.CompanionTheory.CommAlg.FlagIndependence

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagIndependence.Statement := by
  have hPE := PairNumberExpansionIndependence.proof
    GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors.verticalDivisorsCommute
  have hCM : GenericProjClosureModel.Statement :=
    GenericProjClosureModel.proof TwistedDualGensExist.proof
      (GenericProjClosureDim.proof DvrConeDimTrdeg.proof
        (PairBundleTrdeg.proof AdjoinTrdegAdd.proof PairConeLinesIndep.proof PairConeAlg.proof))
      (GenericProjClosureDivisor.proof TwistedDualGensExpress.proof)
  have hFM : SegreFlagClosureModel.Statement :=
    SegreFlagClosureModel.proof (SegreFlagClosureTrdeg.proof SegreFlagConeAlg.proof)
  have hSP := SegreFlagClosurePullback.proof GlobalTheory.T.pair_number_pullback hPE hFM
    PairNumberRelabel.proof VerticalDivisorJoinPullback.proof SegreFlagClosureBirational.proof
  have hSCN := SegreClosureNumber.proof hPE hFM
    GlobalTheory.T.exists_heckeCorrespondence_on_integral_shimuraModel hSP
  exact FlagIndependence.proof hPE (HsymmPairFlagIndependence.proof hPE hCM hSCN)
    SymmetricSpanHsymm.proof

end GlobalTheory.CompanionTheory.CommAlg.FlagIndependence
