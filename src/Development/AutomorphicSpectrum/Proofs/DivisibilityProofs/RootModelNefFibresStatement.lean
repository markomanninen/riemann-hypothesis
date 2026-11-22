module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelNefFibres
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_model_nef_fibres : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N), (∀ k, 0 ≤ M.A.a k) → M.NefFib 0 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.rootModel_nefFib_zero_one_of_nonneg | exact GlobalTheory.CompanionTheory.Ar.Top.rootModel_nefFib_zero_one_of_nonneg | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.rootModel_nefFib_zero_one_of_nonneg <;> assumption)
