module

public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut
namespace PushPf

variable {J' J : Type} [SmallCategory J'] [SmallCategory J] {D' : J' ⥤ PSh} {D : J ⥤ PSh} {G : J' ⥤ J}

def phi (α : D' ⟶ G ⋙ D) (U : Scheme.{0}ᵒᵖ) : (D'.flip.obj U).Elements ⥤ (D.flip.obj U).Elements where
  obj e := (D.flip.obj U).elementsMk (G.obj e.obj) ((α.app e.obj).app U e.val)
  map {e e'} g := Functor.Elements.homMk (G.map g.hom) (by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app (α.naturality g.hom) U) e.val
    exact h.symm.trans (congrArg (fun y => (α.app e'.obj).app U y) g.map_val))
  map_id e := Functor.Elements.hom_ext (G.map_id e.obj)
  map_comp g g' := Functor.Elements.hom_ext (G.map_comp g.hom g'.hom)

theorem elem_ext {X : Type} [Category X] {F : J ⥤ Type} (A B : X ⥤ F.Elements) (ho : ∀ x, A.obj x = B.obj x)
    (hm : A ⋙ Functor.Elements.π F = B ⋙ Functor.Elements.π F) : A = B := by
  refine CategoryTheory.Functor.ext ho (fun x y g => ?_)
  apply (Functor.Elements.π F).map_injective
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  exact Functor.congr_hom hm g

theorem phi_nat (α : D' ⟶ G ⋙ D) {U U' : Scheme.{0}ᵒᵖ} (f : U ⟶ U') :
    phi α U ⋙ (D.flip.map f).mapElements = (D'.flip.map f).mapElements ⋙ phi α U' :=
  elem_ext _ _ (fun e => by
    refine Functor.Elements.ext _ _ rfl ?_
    change (D.flip.obj U').map (𝟙 (G.obj e.obj))
        ((D.obj (G.obj e.obj)).map f ((α.app e.obj).app U e.val)) =
      (α.app e.obj).app U' ((D'.obj e.obj).map f e.val)
    rw [(D.flip.obj U').map_id]
    exact (ConcreteCategory.congr_hom ((α.app e.obj).naturality f) e.val).symm) rfl

def bmap (α : D' ⟶ G ⋙ D) : hoc D' ⟶ hoc D where
  app n :=
    { app := fun U => TypeCat.ofHom fun x => (chn x ⋙ phi α U : Fin (n.unop.len + 1) ⥤ _)
      naturality := fun U U' f => by
        ext x
        change (chn x ⋙ (D'.flip.map f).mapElements) ⋙ phi α U' = (chn x ⋙ phi α U) ⋙ (D.flip.map f).mapElements
        rw [Functor.assoc, Functor.assoc, phi_nat] }
  naturality n m θ := by
    ext U x
    rfl

theorem goal (α : D' ⟶ G ⋙ D) {Y' Y : PSh} (f : Y' ⟶ Y) (c' : ∀ j, D'.obj j ⟶ Y') (c : ∀ j, D.obj j ⟶ Y) (hc' : Coc D' c') (hc : Coc D c)
  (h : ∀ j, α.app j ≫ c (G.obj j) = c' j ≫ f) : bmap α ≫ aug c hc = aug c' hc' ≫ disc.map f := by
  ext n U x
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (h ((chn x).obj 0).obj) U) ((chn x).obj 0).val

end PushPf

theorem LeafPush_of : LeafPush := fun _ _ _ _ _ _ _ α _ _ f c' c hc' hc h => ⟨PushPf.bmap α, PushPf.goal α f c' c hc' hc h⟩

end LateralTheory.CohomologicalPurity.TubeCut
