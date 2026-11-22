module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PushDownOfArithIntersectionSystem
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.push_down_of_arith_intersection_system : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → GroundTheory.Heights₂.Heights.LowerBoundFree.PushDown.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.pushDown | exact GlobalTheory.CompanionTheory.Ar.Giv.pushDown | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.pushDown <;> assumption)
