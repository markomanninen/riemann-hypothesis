module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem ev_triv_congr {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (f : Z1 (O (dp0 R) s))
    {D D' : Type} [CommRing D] [CommRing D'] (i j : Algebra R D) (i' j' : Algebra R D') (hi : i = j) (hi' : i' = j')
    (x : Sp D ⟶ X) (x₁ x₂ : Sp D' ⟶ X) (hx₁ : x₁ = x₂)
    (hx : x ≫ s = spMap (@algebraMap R D _ _ i)) (hxj : x ≫ s = spMap (@algebraMap R D _ _ j))
    (hx' : x₁ ≫ s = spMap (@algebraMap R D' _ _ i')) (hxj' : x₂ ≫ s = spMap (@algebraMap R D' _ _ j'))
    (a : @Thick.triv R _ X s D _ i x hx ⟶ @Thick.triv R _ X s D' _ i' x₁ hx')
    (b : @Thick.triv R _ X s D _ j x hxj ⟶ @Thick.triv R _ X s D' _ j' x₂ hxj')
    (h : ∀ r, a.φ r = b.φ r) : ev f a = ev f b := by
  subst hi hi' hx₁
  have : a = b := Thick.Hom.ext' (AlgHom.ext h)
  subst this
  rfl

theorem ev_functor_map_trivMap {R : Type} [CommRing R] {X Y : Over (Sp R)} (q : Y ⟶ X)
    (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R) (Y.hom ≫ 𝟙 _) (RingHom.id R) q.left)
    (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (D : Type) [CommRing D] [j : Algebra R D] (D' : Type) [CommRing D']
    [j' : Algebra R D'] (φ : D →ₐ[R] D') (y : Pt Y D) :
    ev f (m.functor.map (trivMap φ y)) = ev f (trivMap φ (y ≫ q)) := by
  let y' : Pt Y D' := spOver φ ≫ y
  have h : (y' ≫ q).left = (spOver φ ≫ y ≫ q).left :=
    congrArg (fun p : Pt X D' ↦ p.left) (Category.assoc (spOver φ) y q)
  exact ev_triv_congr f (((algebraMap R D).comp (RingHom.id R)).toAlgebra) j
    (((algebraMap R D').comp (RingHom.id R)).toAlgebra) j' (Algebra.algebra_ext _ _ fun _ ↦ rfl)
    (Algebra.algebra_ext _ _ fun _ ↦ rfl) (y ≫ q).left (y' ≫ q).left
    (spOver φ ≫ y ≫ q).left h (m.obj (trivAt y)).w (Pt.w (y ≫ q))
    (m.obj (trivAt y')).w (Pt.w (spOver φ ≫ y ≫ q))
    (m.functor.map (trivMap φ y)) (trivMap φ (y ≫ q)) fun _ ↦ rfl

theorem fv_pullbackOneCocycle_eq_pull : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (q : Y ⟶ X) (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R) (Y.hom ≫ 𝟙 _) (RingHom.id R) q.left) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))), fv (m.coef.pullbackOneCocycle f) = (fv f).pull q := by
  intro R _ X Y q m f
  funext D _ _ D' _ _ φ y
  change ev f (m.functor.map (trivMap φ y)) = ev f (trivMap φ (y ≫ q))
  exact ev_functor_map_trivMap q m f D D' φ y

end GlobalTheory.PtExt
