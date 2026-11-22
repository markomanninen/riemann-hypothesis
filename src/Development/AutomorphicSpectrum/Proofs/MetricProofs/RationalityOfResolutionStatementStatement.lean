module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RationalityOfResolutionStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationality_of_resolution_statement : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.RatRStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.ratR_of_resK | exact GlobalTheory.CompanionTheory.Ar.Giv.ratR_of_resK | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.ratR_of_resK <;> assumption)
