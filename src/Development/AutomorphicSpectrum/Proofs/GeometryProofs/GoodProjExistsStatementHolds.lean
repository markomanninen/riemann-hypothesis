module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood

@[expose] public section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem goodProjExistsStatement_holds : ReciprocityTheory.ChartRestriction.G.Geo.GoodProjExistsStatement :=
  ReciprocityTheory.ChartRestriction.G.Geo.goodProjExists

end GlobalTheory.CompanionTheory.Ar.Link
