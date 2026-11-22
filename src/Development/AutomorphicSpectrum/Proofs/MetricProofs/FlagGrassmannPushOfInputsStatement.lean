module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGrassmannPushOfInputs
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagGrassPush

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_grassmann_push_of_inputs : GlobalTheory.CompanionTheory.Ar.PB.Inputs → ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → GroundTheory.Heights₂.Heights.LowerBoundFree.FlagGrassPush.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.flagGrassPush | exact GlobalTheory.CompanionTheory.Ar.Giv.flagGrassPush | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.flagGrassPush <;> assumption)
