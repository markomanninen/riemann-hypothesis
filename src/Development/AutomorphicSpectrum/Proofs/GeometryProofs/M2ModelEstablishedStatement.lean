module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.M2ModelEstablished
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CurveSemiAbelianConjecture
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootLineDeRhamModel_holds : RootLineDeRhamModel := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.m2Model_holds | exact GlobalTheory.CompanionTheory.Ar.Conj.m2Model_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.m2Model_holds <;> assumption)
