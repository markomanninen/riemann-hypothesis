module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularAtBaseChange
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_at_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ (f : T → FractionRing R) (g' : Γ'.G.left), Γ.RegularAt f (F g') → Γ'.RegularAt (fun t => κ (f t)) g' := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hF κ hκ f g' ⟨U, hU, s, hs⟩
  refine ⟨F ⁻¹ᵁ U, hU, (F.app U).hom s, fun t h => ?_⟩
  have e := genericPoint_baseChange R T Γ R' Γ' F hF κ hκ t
  let x := (Γ.pt t).left
  let φ := Spec.map (CommRingCat.ofHom κ)
  have hcomp : ⊤ ≤ ((Γ'.pt t).left ≫ F) ⁻¹ᵁ U := h
  have hmap : ⊤ ≤ (φ ≫ x) ⁻¹ᵁ U := e ▸ hcomp
  have hx : ⊤ ≤ x ⁻¹ᵁ U := fun z _ => by
    have hz : z = φ (IsLocalRing.closedPoint (FractionRing R')) :=
      Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
    rw [hz]
    exact hmap (by trivial)
  have valAt_eq {y y' : Spec (CommRingCat.of (FractionRing R')) ⟶ Γ.G.left}
      (hy : ⊤ ≤ y ⁻¹ᵁ U) (hy' : ⊤ ≤ y' ⁻¹ᵁ U) (eq : y = y') :
      valAt y U hy s = valAt y' U hy' s := by
    subst y'
    rfl
  have happ : (φ ≫ x).appLE U ⊤ hmap = x.appLE U ⊤ hx ≫ φ.appTop := by
    rw [← Scheme.Hom.appLE_comp_appLE φ x U ⊤ ⊤ hx le_top]
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE φ]
    rfl
  calc
    _ = valAt ((Γ'.pt t).left ≫ F) U hcomp s := by
      simp only [valAt, Scheme.Hom.comp_appLE]
      rfl
    _ = valAt (φ ≫ x) U hmap s := valAt_eq hcomp hmap e
    _ = κ (valAt x U hx s) := by
      simp only [valAt, happ]
      exact congrArg (fun z => z.hom ((x.appLE U ⊤ hx).hom s))
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom κ))
    _ = κ (f t) := congrArg κ (hs t hx)
