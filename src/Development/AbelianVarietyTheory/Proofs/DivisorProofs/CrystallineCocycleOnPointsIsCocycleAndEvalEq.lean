module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem ev_eq_fv_of_triv {R : Type} [CommRing R] {X : Over (Sp R)} (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _)))
    (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (x : Pt X D) (x' : Pt X D')
    (φ : D →ₐ[R] D') (a : trivAt x ⟶ trivAt x') (h : ∀ r : D, a.φ r = φ r) :
    spOver φ ≫ x = x' ∧ ev f a = fv f D D' φ x := by
  have e : spOver φ ≫ x = x' := by
    have h0 : a.φ₀ = (φ : D →+* D') := RingHom.ext fun r ↦ (a.comm r).trans (h r)
    have hp := a.pt
    rw [h0] at hp
    exact Over.OverMorphism.ext hp
  subst x'
  refine ⟨rfl, ?_⟩
  have ha : a = trivMap φ x := Thick.Hom.ext' (AlgHom.ext h)
  exact congrArg (ev f) ha

theorem fv_isCoc_and_ev_eq :
    ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))),
      IsCoc (whole X) (fv f) ∧
        ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
          (x : Pt X D) (x' : Pt X D') (φ : D →ₐ[R] D') (a : trivAt x ⟶ trivAt x'),
          (∀ r : D, a.φ r = φ r) → spOver φ ≫ x = x' ∧ ev f a = fv f D D' φ x := by
  intro R _ X f
  refine ⟨?_, fun D _ _ D' _ _ x x' φ a h ↦ ev_eq_fv_of_triv f D D' x x' φ a h⟩
  intro D _ _ D' _ _ D'' _ _ φ ψ x _
  let y : Pt X D' := spOver φ ≫ x
  let z : Pt X D'' := spOver ψ ≫ y
  have h := (ev_eq_fv_of_triv f D D'' x z (ψ.comp φ)
    (trivMap φ x ≫ trivMap ψ y) (fun _ ↦ rfl)).2
  exact h.symm.trans (ev_comp f (trivMap φ x) (trivMap ψ y))

end GlobalTheory.PtExt
