module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfResolutionGaga
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_theorem_of_resolution_gaga : Geo.ResK.ResKStatement → GagaSections → PartI → ThmFlatA := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.thmFlatA_of_resK_gaga_partI | exact GlobalTheory.CompanionTheory.Ar.Flat.thmFlatA_of_resK_gaga_partI | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.thmFlatA_of_resK_gaga_partI <;> assumption)
