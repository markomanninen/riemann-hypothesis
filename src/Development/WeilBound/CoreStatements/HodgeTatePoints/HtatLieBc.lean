module

public import Mathlib
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLie
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinearStatement

@[expose] public section

noncomputable section

namespace PositivityTheory.HtPt.Htat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem lie_fin : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R] (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), Module.Finite R E ∧ Module.Projective R E := by
  intro S G _ _ R _ x E _ _ M
  exact ⟨(lie_proj S G R x E M).1, (lie_proj S G R x E M).2.1⟩

theorem lie_bc : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) E'), ∃ j : E →+ E', (∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M.pt e).left) ∧ (∀ (a : R) e, j (a • e) = algebraMap R R' a • j e) ∧ (Smooth G.hom → ∀ (n : ℕ) (b : Module.Basis (Fin n) R E), LinearIndependent R' (fun k => j (b k)) ∧ Submodule.span R' (Set.range fun k => j (b k)) = ⊤) := by
  intro S G _ R R' _ _ _ x E E' _ _ _ _ M M'
  obtain ⟨j, hj, -⟩ := LieBaseChange.existsUnique_semilinear_lifts S G R R' (algebraMap R R') x E E' M M'
  refine ⟨j.toAddMonoidHom, fun e => ?_, fun a e => j.map_smulₛₗ a e, fun hsm n b => ?_⟩
  · have := hj e
    simp only [Category.comp_id] at this
    exact this
  · haveI : Smooth G.hom := hsm
    letI : Module R E' := Module.compHom E' (algebraMap R R')
    haveI : IsScalarTower R R' E' := ⟨fun a c v => by
      show (a • c) • v = algebraMap R R' a • c • v
      rw [Algebra.smul_def, mul_smul]⟩
    let β : E →ₗ[R] E' :=
      { toFun := j
        map_add' := j.map_add
        map_smul' := fun a e => j.map_smulₛₗ a e }
    have hb := Lie.isBaseChange_lie x M R' E' M' β (fun e => by
      have := hj e
      simp only [Category.comp_id] at this
      exact this)
    have hbk : ∀ k, hb.basis b k = j (b k) := fun k => by
      rw [IsBaseChange.basis_apply]
      rfl
    have hfun : (fun k => j.toAddMonoidHom (b k)) = ⇑(hb.basis b) := funext fun k => (hbk k).symm
    refine ⟨?_, ?_⟩
    · rw [hfun]
      exact (hb.basis b).linearIndependent
    · rw [hfun]
      exact (hb.basis b).span_eq

end PositivityTheory.HtPt.Htat
