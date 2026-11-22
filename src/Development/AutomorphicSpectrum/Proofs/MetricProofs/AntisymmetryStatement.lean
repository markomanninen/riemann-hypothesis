module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Antisymmetry
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antisymmetry' : Antisymmetry := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Top.antisymmetry | exact GlobalTheory.CompanionTheory.Ar.PB.Top.antisymmetry | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Top.antisymmetry <;> assumption)
