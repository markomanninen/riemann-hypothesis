module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseMetricExistsOfGiven
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_metric_exists_of_given : Given → PB.BaseMetricExists := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.BMx.baseMetricExists_of_given | exact GlobalTheory.CompanionTheory.Ar.PB.BMx.baseMetricExists_of_given | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.BMx.baseMetricExists_of_given <;> assumption)
