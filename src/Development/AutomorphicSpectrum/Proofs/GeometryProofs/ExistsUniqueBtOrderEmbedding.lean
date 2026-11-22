module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsDenOfOpen

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

open PositivityTheory.HtPt.Mh in
theorem exists_unique_emb_btOrder_top : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), ∃! j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤)), Γ.IsEmb (Γ.btOrder ⊤) j := by
  intro R _ _ T _ _ Γ
  let A := Γ.btOrder ⊤
  have htop (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ ⊤) (s : Γ(Γ.G.left, ⊤)) :
      valAt (Γ.pt t).left ⊤ h s = val (Γ.pt t).left s := by
    simp only [valAt, val, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have hsec (a : A) : ∃ s : Γ(Γ.G.left, ⊤), ∀ t,
      val (Γ.pt t).left s = algebraMap R (FractionRing R) (a.1 t) := by
    have ha := (PositivityTheory.HtPt.Twhopf.mem_order R T Γ ⊤ a.1).1 a.2
    obtain ⟨s, hs⟩ := (PositivityTheory.HtPt.Twhopf.reg_iff R T Γ ⊤ _).1 (ha 1)
    refine ⟨s, fun t => (htop t le_top s).symm.trans ?_⟩
    simpa only [_root_.one_mul] using hs t le_top
  have hsec_ext {s s' : Γ(Γ.G.left, ⊤)}
      (h : ∀ t, val (Γ.pt t).left s = val (Γ.pt t).left s') : s = s' := by
    rw [← sub_eq_zero]
    refine PositivityTheory.HtPt.Twhopf.sec_inj R T Γ ⊤ _ fun t ht => ?_
    rw [htop, map_sub, h, sub_self]
  have hhom_ext {B : Type} [CommRing B] {j j' : Γ.G.left ⟶ Spec (CommRingCat.of B)}
      (h : ∀ t, (Γ.pt t).left ≫ j = (Γ.pt t).left ≫ j') : j = j' :=
    pb_ext fun a => hsec_ext fun t => by rw [val_pb_comp, h, ← val_pb_comp]
  choose s hs using hsec
  let φ : A →+* Γ(Γ.G.left, ⊤) :=
    { toFun := s
      map_one' := hsec_ext fun t => by rw [hs, map_one]; simp
      map_mul' := fun a b => hsec_ext fun t => by rw [hs, map_mul, hs, hs]; simp
      map_zero' := hsec_ext fun t => by rw [hs, map_zero]; simp
      map_add' := fun a b => hsec_ext fun t => by rw [hs, map_add (f := _), hs, hs]; simp }
  obtain ⟨j, hj⟩ := exists_pb φ
  have hpt : ∀ t, (Γ.pt t).left ≫ j = Spec.map (CommRingCat.ofHom
      ((algebraMap R (FractionRing R)).comp
        ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom))) := by
    intro t
    apply comp_eq_spec
    intro a
    rw [hj]
    exact hs a t
  refine ⟨j, ⟨?_, hpt⟩, fun j' hj' => hhom_ext fun t => by rw [hj'.pt, hpt]⟩
  apply hhom_ext
  intro t
  rw [← Category.assoc, hpt, spec_comp, Over.w (Γ.pt t)]
  show _ = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  congr 2

end GlobalTheory.CompanionTheory.Ar.BT
