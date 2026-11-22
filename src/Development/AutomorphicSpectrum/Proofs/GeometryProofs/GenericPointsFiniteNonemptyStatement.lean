module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCover
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsFiniteNonempty
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
theorem _root_.GlobalTheory.T.generic_points_finite_nonempty :
    _root_.GlobalTheory.CompanionTheory.Ar.Top.Given →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
      (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)),
      {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Finite ∧
      {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Nonempty := by
  intro hG E _ _ _ H D l Xo c Y
  have : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have : TopologicalSpace.NoetherianSpace Y.X := GlobalTheory.ModelSum.noetherianSpace_of_isProjOver Y.proj
  have : Nonempty Y.X := Comps.model_nonempty Y (Comps.moduli_nonempty hG.1.2.2.1 Xo)
  exact ⟨Comps.finite_maximal_points Y.X, Comps.nonempty_maximal_points Y.X⟩
