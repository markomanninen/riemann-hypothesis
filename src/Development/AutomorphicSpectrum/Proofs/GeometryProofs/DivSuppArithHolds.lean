module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp

@[expose] public section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem divSuppArith_holds : ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement :=
  ReciprocityTheory.ChartRestriction.G.Geo.divSuppArith

end GlobalTheory.CompanionTheory.Ar.Link
