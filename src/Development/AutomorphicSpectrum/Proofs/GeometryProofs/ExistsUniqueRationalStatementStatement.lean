module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueRationalStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement

@[expose] public section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_rational_statement : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Link.existsUnique_rat | exact GlobalTheory.CompanionTheory.Ar.Link.existsUnique_rat | (intros; apply GlobalTheory.CompanionTheory.Ar.Link.existsUnique_rat <;> assumption)
