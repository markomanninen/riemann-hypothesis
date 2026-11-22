module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChangeStatement

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_isBaseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (E' : Type) [AddCommGroup E'] [Module R' E'] [Module R E'] [IsScalarTower R R' E'] (M : LieModel G x E) (M' : LieModel G (spMap (algebraMap R R') ≫ x) E') (j : E →ₗ[R] E'), (∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left)) → IsBaseChange R' j := by
  intro S G _ _ R R' _ _ _ x E _ _ E' _ _ _ _ M M' j hj
  refine (GlobalTheory.T.lie_model_finite_base_change S G R x E M).2.2 R' E' M' j fun e => ?_
  have h := hj e
  change _ ≫ _ = _ ≫ _ at h
  rw [Category.comp_id] at h
  exact h

end GlobalTheory.CompanionTheory.Ar
