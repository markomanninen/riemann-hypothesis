module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedDescendsToFinitelyGenerate

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
theorem _root_.GlobalTheory.T.geometricallyConnected_descends_to_finitelyGenerated : ∀ (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsProper G.hom → GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k V))) → ∃ R : Subalgebra k V, R.FG ∧ GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k R))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_descends_to_fg | exact GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_descends_to_fg | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_descends_to_fg <;> assumption)
