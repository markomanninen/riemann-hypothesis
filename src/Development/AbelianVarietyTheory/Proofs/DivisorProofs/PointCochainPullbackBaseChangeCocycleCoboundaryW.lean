module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {X : Over (Sp R)} {X' : Over (Sp R')}
  {q : X'.left ⟶ X.left}

theorem ptVia_spOver (w : q ≫ X.hom = X'.hom ≫ spMap σ) {E E' : Type} [CommRing E] [Algebra R' E]
    [CommRing E'] [Algebra R' E'] (φ : E →ₐ[R'] E') (y : Pt X' E) :
    ptVia w (spOver φ ≫ y) =
      @spOver R _ E E' _ (algVia σ E) _ (algVia σ E') (homVia σ φ) ≫ ptVia w y := by
  apply Over.OverMorphism.ext
  change (spMap (φ : E →+* E') ≫ y.left) ≫ q = spMap (φ : E →+* E') ≫ (y.left ≫ q)
  exact Category.assoc _ _ _

theorem bcPull_coc_cob (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X) :
    (IsCoc (whole X) u → IsCoc (whole X') (bcPull w u)) ∧
      ((∃ k, IsCob (whole X) u k) → ∃ k, IsCob (whole X') (bcPull w u) k) := by
  constructor
  · intro h
    unfold IsCoc at h ⊢
    intro E _ _ E' _ _ E'' _ _ φ ψ y _
    let _ : Algebra R E := algVia σ E
    let _ : Algebra R E' := algVia σ E'
    let _ : Algebra R E'' := algVia σ E''
    have hc : (homVia σ ψ).comp (homVia σ φ) = homVia σ (ψ.comp φ) := AlgHom.ext fun _ ↦ rfl
    simp only [bcPull, ptVia_spOver, ← hc]
    exact h E E' E'' (homVia σ φ) (homVia σ ψ) (ptVia w y) (sm_whole _)
  · rintro ⟨k, hk⟩
    refine ⟨fun E _ _ y ↦ @k E _ (algVia σ E) (ptVia w y), ?_⟩
    unfold IsCob at hk ⊢
    intro E _ _ E' _ _ φ y _
    let _ : Algebra R E := algVia σ E
    let _ : Algebra R E' := algVia σ E'
    simp only [bcPull, ptVia_spOver]
    exact hk E E' (homVia σ φ) (ptVia w y) (sm_whole _)

theorem bcPull_keeps : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X : Over (Sp R)) (X' : Over (Sp R')) (q : X'.left ⟶ X.left) (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X), (IsCoc (whole X) u → IsCoc (whole X') (bcPull w u)) ∧ ((∃ k, IsCob (whole X) u k) → ∃ k, IsCob (whole X') (bcPull w u) k) :=
  fun _ _ _ _ _ _ _ _ w u ↦ bcPull_coc_cob w u

end GlobalTheory.PtExt
