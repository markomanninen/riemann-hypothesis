module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PoincareLelong.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableAbsFibreSumOfIsCxVar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegreChartIntegralHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDivisorCompare
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DivisorGeneralPointBranches
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LelongLimitAtBranches
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceReducedAwayZariski
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheetIdentityAll

@[expose] public section

namespace PositivityTheory.Tls2.Pl

theorem poincareLelong : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong :=
  poincareLelong_of_leaves GlobalTheory.CompanionTheory.Ar.Pub.CxAbs.ptsAbsIntegrable GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral
    GlobalTheory.CompanionTheory.Ar.chartDivisorCompare GlobalTheory.CompanionTheory.ComplexSets.divisorGeneralPointBranches
    GlobalTheory.CompanionTheory.Ar.Lelong.lelongLimitAtBranches GlobalTheory.CompanionTheory.Heights.BranchOrder.localOrder
    GlobalTheory.CompanionTheory.VarLelong.regMassNearSmall

theorem poincareLelongInv : GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv :=
  poincareLelongInv_of_leaves GlobalTheory.CompanionTheory.Ar.Pub.CxAbs.ptsAbsIntegrable GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral
    GlobalTheory.CompanionTheory.Ar.chartDivisorCompare GlobalTheory.CompanionTheory.ComplexSets.divisorGeneralPointBranches
    GlobalTheory.CompanionTheory.Ar.Lelong.lelongLimitAtBranches GlobalTheory.CompanionTheory.Heights.BranchOrder.localOrder
    GlobalTheory.CompanionTheory.VarLelong.regMassNearSmall

end PositivityTheory.Tls2.Pl
