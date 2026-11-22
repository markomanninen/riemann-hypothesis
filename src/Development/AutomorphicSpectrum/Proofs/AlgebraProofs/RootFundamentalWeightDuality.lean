module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.HFundinv

@[expose] public section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem rootOnFund_mul_fundOnRoot_inverse : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (r r' : Ψ × Fin N), (∑ a, rootOnFund r a * fundOnRoot a r' = if r = r' then 1 else 0) ∧ (∀ π : Ψ ≃ Ψ, rootOnFund (π r.1, r.2) (π r'.1, r'.2) = rootOnFund r r' ∧ fundOnRoot (π r.1, r.2) (π r'.1, r'.2) = fundOnRoot r r') :=
  @PositivityTheory.UnitarySelfGeneration.h_fundinv

end GlobalTheory.CompanionTheory.Ar.Cmp
