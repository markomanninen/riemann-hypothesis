module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberMultilinearSymm
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_number_multilinear_symm : ∀ (K : Type) [Field K] (A : AbVar K) (J : Type) [Fintype J], Fintype.card J = A.dim → (∃ M : MultilinearMap (RingHom.id ℤ) (fun _ : J => Pic A.X.left) ℤ, ∀ c, M c = inter A c) ∧ ∀ (J' : Type) [Fintype J'] (e : J' ≃ J) (c : J → Pic A.X.left), inter A (c ∘ e) = inter A c := by
  intro K _ A J _ hJ
  classical
  have hMultilinear : ∃ M : MultilinearMap (RingHom.id ℤ) (fun _ : J => Pic A.X.left) ℤ,
      ∀ c, M c = inter A c := by
    refine ⟨MultilinearMap.mk' (fun c => inter A c) (inter_update_add A hJ) ?_, fun c => rfl⟩
    intro c i n a
    exact map_zsmul (interAdd A hJ c i) n a
  exact ⟨hMultilinear, fun J' _ e c => inter_comp_equiv A e c⟩
