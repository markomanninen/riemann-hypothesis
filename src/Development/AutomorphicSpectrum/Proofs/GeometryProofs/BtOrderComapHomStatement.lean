module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderComapHom
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.btOrder_comap_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (T' : Type) [CommGroup T'] [Finite T'] (Γ' : QFGroup R T') (a : Γ.G ⟶ Γ'.G) (α : T →* T'), (∀ t, Γ.pt t ≫ a = Γ'.pt (α t)) → ∀ f ∈ Γ'.btOrder ⊤, (fun t => f (α t)) ∈ Γ.btOrder ⊤ := by
  intro R _ _ T _ _ Γ T' _ _ Γ' a α ha f hf
  let Φ : (T' → R) →ₐ[R] (T → R) :=
    { toFun := fun f t => f (α t)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hle : Γ'.btOrder ⊤ ≤ (Γ.btOrder ⊤).comap Φ := by
    refine Algebra.adjoin_le fun f hf => ?_
    refine Algebra.subset_adjoin fun t g _ => ?_
    obtain ⟨U, hU, s, hs⟩ := hf (α t) (a.left g) trivial
    refine ⟨a.left ⁻¹ᵁ U, hU, (a.left.app U).hom s, fun x h => ?_⟩
    have hx : (Γ.pt x).left ≫ a.left = (Γ'.pt (α x)).left := by
      rw [← ha x, Over.comp_left]
    have h' : ⊤ ≤ (Γ'.pt (α x)).left ⁻¹ᵁ U := by
      rw [← hx]
      exact h
    have hval : valAt (Γ.pt x).left (a.left ⁻¹ᵁ U) h ((a.left.app U).hom s) =
        valAt (Γ'.pt (α x)).left U h' s := by
      simp only [valAt, ← hx, Scheme.Hom.comp_appLE]
      rfl
    change valAt (Γ.pt x).left (a.left ⁻¹ᵁ U) h ((a.left.app U).hom s) =
      algebraMap R (FractionRing R) (f (α (t * x)))
    rw [hval, map_mul]
    exact hs (α x) h'
  exact hle hf
