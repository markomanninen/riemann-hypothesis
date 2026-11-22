module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.AbelianSchemeSpreadsOverLocalization

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem abelianTriple_spreads_out : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (tL : SAB H (Sp L)), IsProper tL.G.hom → ∃ (n : 𝓞 L) (_ : n ≠ 0) (T : SAB H (Sp (Localization.Away n))) (f : Localization.Away n →+* L), (∀ x : 𝓞 L, f (algebraMap _ _ x) = (x : L)) ∧ Nonempty (SABMap tL T (spMap f)) :=
  PositivityTheory.Xgn.abelian_scheme_spreads_over_localization

end GlobalTheory.CompanionTheory.Ar.Flat
