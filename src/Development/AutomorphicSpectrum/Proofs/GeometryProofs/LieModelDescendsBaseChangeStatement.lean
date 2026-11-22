module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelDescendsBaseChange
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecStalkSpecializesComp
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChangeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_descends_base_change : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ S) (E' : Type) [AddCommGroup E'] [Module R' E'] [Module R E'] [IsScalarTower R R' E'] (M' : LieModel G (spMap (algebraMap R R') ≫ x) E'), ∃ (E : Type) (_ : AddCommGroup E) (_ : Module R E) (M : LieModel G x E) (j : E →ₗ[R] E'), IsBaseChange R' j ∧ ∀ e, (M'.pt (j e)).left = spMap (dualMap (algebraMap R R')) ≫ (M.pt e).left := by
  exact @GlobalTheory.CompanionTheory.Ar.LieBaseChange.exists_isBaseChange
