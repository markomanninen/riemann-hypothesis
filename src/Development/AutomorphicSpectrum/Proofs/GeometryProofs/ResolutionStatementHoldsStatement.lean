module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ResolutionStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement

@[expose] public section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.resolution_statement_holds : ReciprocityTheory.ChartRestriction.G.Geo.ResBridgeStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Link.resBridgeStatement_holds | exact GlobalTheory.CompanionTheory.Ar.Link.resBridgeStatement_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Link.resBridgeStatement_holds <;> assumption)
