module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GrassmannHeightZ2OfInputsAndZ2
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
theorem _root_.GlobalTheory.T.grassmann_height_Z2_of_inputs_and_Z2 : GlobalTheory.CompanionTheory.Ar.PB.Inputs → ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → SuccessiveMinimaUpperBound → GroundTheory.Heights₂.Heights.LowerBoundFree.GrassmannianHeightZTwo.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.grassmann_height_Z2_of_push | exact GlobalTheory.CompanionTheory.Ar.Giv.grassmann_height_Z2_of_push | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.grassmann_height_Z2_of_push <;> assumption)
