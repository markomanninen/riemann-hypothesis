module

public import Mathlib
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelongInv
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PoincareLelongAlt
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PotFinCons
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.LogRegLineTensor
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLelongSectionLimit
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLelongChartLimit
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsIntegrable
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Stokes
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsBilinear
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChart
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartSectionNotMem
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLelongWeightLimit
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLocalMultComap
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PVarIntGraphX
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PStokesOnVariety
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffLimit
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOff
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffTube
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeEuclMass
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepMass
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepRankOne
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepAreaCount
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimit
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitOnZero
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitGoodPoints
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongMassNearSmall
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.CentredDiscCoverCurveHolds
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.UniformIntegrabilityProportionalityHolds
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.IsolatedPointsCount
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDivisor
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartIntegral

@[expose] public section

namespace PositivityTheory.Tls2.Pl

open GroundTheory.Heights₂.Heights

theorem stokesOnVariety : GroundTheory.Heights₂.Heights.StokesOnVariety.Statement := by
  have hDeep : TubeDeepMass.Statement :=
    TubeDeepMass.proof TubeDeepRankOne.proof
      (TubeDeepAreaCount.proof AutoClose.IsolatedPointsCount)
      HilbertSamuel.Closed.TubeDeepWeightMass
  exact StokesOnVariety.of_open HilbertSamuel.Closed.SheetImageAreaSet
    (TubeEuclMass.proof HilbertSamuel.Closed.TubeCollarMass hDeep)

theorem lelongLimit (hBr : GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches.Statement)
    (hLim : GroundTheory.Heights₂.Heights.LelongLimitAtBranches.Statement)
    (hOrd : GroundTheory.Heights₂.Heights.LocalOrder.Statement)
    (hReg : GroundTheory.Heights₂.Heights.RegMassNearSmall.Statement) :
    GroundTheory.Heights₂.Heights.LelongLimit.Statement := by
  have hGood : LelongLimitGoodPoints.Statement := LelongLimitGoodPoints.proof hBr hLim hOrd
  have hMass : LelongMassNearSmall.Statement :=
    LelongMassNearSmall.proof hReg AutoClose.VarMassNearSmall
  exact LelongLimit.proof AutoClose.LelongLimitOffZero
    (LelongLimitOnZero.proof AutoClose.LelongLimitOffZero hGood hMass AutoClose.VarIntAdd)
    AutoClose.VarIntAdd

theorem lelongPolyLimit (hL : GroundTheory.Heights₂.Heights.LelongLimit.Statement) :
    GroundTheory.Heights₂.Heights.Targets.LelongPolyLimit.Statement :=
  GroundTheory.Heights₂.Heights.Targets.LelongPolyLimit.of_mult_weight GroundTheory.Heights₂.Heights.Targets.LocalMultComap.proof
    (GroundTheory.Heights₂.Heights.Targets.LelongWeightLimit.proof hL stokesOnVariety
      GroundTheory.Heights₂.Heights.AutoClose.Targets_LelongWeightDiff)

theorem ptsAbsMeasurable (hAbs : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement) :
    GroundTheory.Heights₂.Heights.Inter.PtsAbsMeasurable.Statement :=
  fun K _ ι _ P e Ψ L A s h1 h2 h3 h4 h5 => (hAbs K ι P e Ψ L A s h1 h2 h3 h4 h5).aestronglyMeasurable

theorem poincareLelong_of (hAbs : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement)
    (hSCI : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement)
    (hCDC : GroundTheory.Heights₂.Heights.Targets.ChartDivisorCompare.Statement)
    (hLPL : GroundTheory.Heights₂.Heights.Targets.LelongPolyLimit.Statement) : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong := by
  have hPI : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement :=
    PtsIntegrable.of_found hAbs HilbertSamuel.Closed.PtsSumMeasurable
  have hStk : ReciprocityTheory.ChartRestriction.G.Geo.StokesStatement :=
    StokesStatement.of_found (PtsBilinear.proof hAbs HilbertSamuel.Closed.PtsSumMeasurable)
      HilbertSamuel.Closed.SegrePartition
      (SegreChart.proof HilbertSamuel.Closed.SegreChartDim hSCI) stokesOnVariety
  have hChart : Targets.LelongChartLimit.Statement :=
    Targets.LelongChartLimit.proof hSCI HilbertSamuel.Closed.SegreChartDim
      Targets.ChartSectionNotMem.proof hLPL hCDC
  exact Targets.PoincareLelongAlt.of_found hStk (Targets.PoincareLelongRegularised.proof hPI (ptsAbsMeasurable hAbs))
    (Targets.PoincareLelongLimit.proof hPI (Targets.LelongSectionLimit.proof hPI hChart))

theorem poincareLelong_of_leaves (hAbs : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement)
    (hSCI : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement)
    (hCDC : GroundTheory.Heights₂.Heights.Targets.ChartDivisorCompare.Statement)
    (hBr : GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches.Statement)
    (hLim : GroundTheory.Heights₂.Heights.LelongLimitAtBranches.Statement)
    (hOrd : GroundTheory.Heights₂.Heights.LocalOrder.Statement)
    (hReg : GroundTheory.Heights₂.Heights.RegMassNearSmall.Statement) : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong :=
  poincareLelong_of hAbs hSCI hCDC (lelongPolyLimit (lelongLimit hBr hLim hOrd hReg))

theorem poincareLelongInv_of_leaves (hAbs : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement)
    (hSCI : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement)
    (hCDC : GroundTheory.Heights₂.Heights.Targets.ChartDivisorCompare.Statement)
    (hBr : GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches.Statement)
    (hLim : GroundTheory.Heights₂.Heights.LelongLimitAtBranches.Statement)
    (hOrd : GroundTheory.Heights₂.Heights.LocalOrder.Statement)
    (hReg : GroundTheory.Heights₂.Heights.RegMassNearSmall.Statement) : GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv := by
  intro K _ ι _ P n L A B s hP hL hA hB _ _ _ hB0 hs
  have h : ReciprocityTheory.ChartRestriction.G.Geo.ArithmeticPoincareLelongFormula :=
    poincareLelong_of_leaves hAbs hSCI hCDC hBr hLim hOrd hReg
  exact h K ι P n L A B s hP hL hA hB hB0 hs

end PositivityTheory.Tls2.Pl
