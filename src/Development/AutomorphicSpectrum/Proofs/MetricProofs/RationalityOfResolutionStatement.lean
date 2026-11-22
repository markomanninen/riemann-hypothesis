module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatement

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem ratR_of_resK :
    ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.RatRStatement :=
  fun h => GroundTheory.Heights₂.Heights.Inter.RatR.proof (ptsIntegrable_of_resK h)

end GlobalTheory.CompanionTheory.Ar.Giv
