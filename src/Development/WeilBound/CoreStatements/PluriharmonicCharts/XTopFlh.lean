module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FormPolyIsHomogeneousAndEval
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.IsBlockMapOmitV
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.FlHeightNonnegDominant

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem PositivityTheory.Xgp.t_top_flh : FlagHeight := by
  intro hI II hII Ψ _ _ _ N hN
  exact ⟨(GlobalTheory.CompanionTheory.Ar.PB.formPoly_isHomogeneous_and_eval _ _ _).1, PositivityTheory.Xgp.block_hermitian_pullback.flZero_main hI II hII Ψ N hN,
    PositivityTheory.Xgp.block_hermitian_pullback.flHeight_nonneg_dominant hI II hII Ψ N hN⟩
