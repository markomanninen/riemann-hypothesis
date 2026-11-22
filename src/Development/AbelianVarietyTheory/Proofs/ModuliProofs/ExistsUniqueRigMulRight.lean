module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.CubicalSymmetricTriv
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAffineWeightUnits

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.UU GlobalTheory.IndefiniteRowSideFullHecke.CubicalSymmetricTriv
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CubCompare
variable {S S' : Scheme.{0}}

section Gen
variable {X X' Y Y' : Scheme.{0}} {K : Type} [Fintype K]

end Gen

section Pack
variable {G : Over S} [GrpObj G] [IsCommMonObj G]

end Pack

section Maps
variable {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

end Maps

section Triv
variable {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]


variable {L : RigLB G} {i : H ⟶ G}




variable {c : CubicalStr G L} [IsMonHom i]


end Triv

section Wt
variable {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G]

theorem gs_appLE {Y Z : Scheme.{0}} (r : Z ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ r ⁻¹ᵁ V) (u : Γ(Y, V)) (z : Z) :
    gs (𝟙 Z) z ⊤ ((r.appLE V ⊤ h).hom u) = gs r z V u :=
  (gs_res (𝟙 Z) z h trivial _).trans ((gs_pull (𝟙 Z) r z V (h trivial) u).trans (by rw [Category.id_comp]))

theorem gs_comp {Y Z Z' : Scheme.{0}} (ρ : Z' ⟶ Z) (r : Z ⟶ Y) (V : Y.Opens) (z : Z') (h : r (ρ z) ∈ V) (u : Γ(Y, V)) :
    gs (ρ ≫ r) z V u = (ρ.stalkMap z).hom (gs r (ρ z) V u) := by
  rw [gs_eq (ρ ≫ r) z V h, gs_eq r _ V h]
  exact (Scheme.Hom.germ_stalkMap_apply ρ (r ⁻¹ᵁ V) z h _).symm

theorem isWt_iff_germ (i : splitTorus S X ⟶ G) (V : G.left.Opens) (u : Γ(G.left, V)) (χ : X) :
    IsWt i V u χ ↔ ∀ (T : Over S) (z : T.left) (t : T ⟶ splitTorus S X) (x : T ⟶ G), x.left z ∈ V →
      ((t ≫ i) * x).left z ∈ V → gs ((t ≫ i) * x).left z V u = (charV χ z t).val * gs x.left z V u := by
  have key : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V) (z : Z.left),
      gs (𝟙 Z.left) z ⊤ (t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom u) =
        (charV χ z t).val * gs g.left z V u := fun Z t g h₂ z => by
    rw [gs_mul _ z ⊤ trivial, gs_appLE, ← chV_val, gs_unit _ z ⊤ trivial, charV, gm_charUnit]
  constructor
  · intro h T z t x hx hx'
    let O : T.left.Opens := x.left ⁻¹ᵁ V ⊓ ((t ≫ i) * x).left ⁻¹ᵁ V
    let ρ : Over.mk (O.ι ≫ T.hom) ⟶ T := Over.homMk O.ι rfl
    have e : ((ρ ≫ t) ≫ i) * (ρ ≫ x) = ρ ≫ ((t ≫ i) * x) := by rw [MonObj.comp_mul, Category.assoc]
    have h₁ : ⊤ ≤ (((ρ ≫ t) ≫ i) * (ρ ≫ x)).left ⁻¹ᵁ V := by rw [e]; exact fun y _ => y.2.2
    have h₂ : ⊤ ≤ (ρ ≫ x).left ⁻¹ᵁ V := fun y _ => y.2.1
    have a := congrArg (gs (𝟙 _) (⟨z, hx, hx'⟩ : O) ⊤) (h _ (ρ ≫ t) (ρ ≫ x) h₁ h₂)
    erw [key, gs_appLE] at a
    rw [e] at a
    unfold charV at a
    erw [← gs_unit _ _ ⊤ trivial] at a
    have inj : ∀ y : O.toScheme, Function.Injective (O.ι.stalkMap y).hom := fun y =>
      (ConcreteCategory.bijective_of_isIso _).1
    apply inj ⟨z, hx, hx'⟩
    rw [charV, ← gs_unit _ _ ⊤ trivial]
    exact ((gs_comp O.ι _ V ⟨z, hx, hx'⟩ hx' u).symm.trans a).trans ((congrArg₂ (· * ·)
      (gs_comp O.ι t.left ⊤ ⟨z, hx, hx'⟩ trivial _) (gs_comp O.ι x.left V ⟨z, hx, hx'⟩ hx u)).trans (map_mul _ _ _).symm)
  · intro h Z t g h₁ h₂
    refine fn_ext fun z _ => ?_
    rw [key, gs_appLE]
    exact h Z z t g (h₂ trivial) (h₁ trivial)

end Wt

section Ext
variable {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G]

variable {B : Over S} [GrpObj B]


end Ext

section Desc
variable {G H B : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] [GrpObj B] [IsCommMonObj B]
  {i : H ⟶ G} [IsMonHom i] {q : G ⟶ B} [IsMonHom q] {P : CP G} {M : CP B} {w : LB.Iso P.L.L (M.L.L.pull q.left)}



end Desc

end GlobalTheory.CubCompare
end
