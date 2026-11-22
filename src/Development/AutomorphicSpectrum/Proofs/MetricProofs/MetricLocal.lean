module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.MetricLocalB

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem metricLocal : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement :=
  GroundTheory.Heights₂.Heights.MetricLocalB.full

end GlobalTheory.CompanionTheory.Ar.Giv
