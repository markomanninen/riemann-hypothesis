module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeSheafHomValueAtCechNerveSimplexBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (Y X : Scheme.{0}) (f : Y ⟶ X) (k : ℕ) (Z : Scheme.{0}) (x : Z ⟶ X) (y : Fin (k + 1) → (Z ⟶ Y)) (h : ∀ i, y i ≫ f = x), IsLimit (WidePullbackCone.mk (f := fun _ : Fin (k + 1) => f) x y h) → Function.Bijective (fun s : (free R).obj ((cech f).obj (op (SimplexCategory.mk k))) ⟶ F => GlobalTheory.EtC.val s Z (cechPt f k x y h)) := by
  intro R _ F Y X f k Z x y h hc
  have e : ∀ U : Scheme.{0}, Function.Bijective
      (fun g : U ⟶ Z => ((cech f).obj (op (SimplexCategory.mk k))).map g.op (cechPt f k x y h)) := by
    intro U
    have hb := CechPts.bij f k x y h hc U
    refine ⟨fun g g' hg => hb.1 ((CechPts.map_cechPt f k x y h g).symm.trans (hg.trans (CechPts.map_cechPt f k x y h g'))), fun v => ?_⟩
    obtain ⟨g, hg⟩ := hb.2 v
    exact ⟨g, (CechPts.map_cechPt f k x y h g).trans hg⟩
  let P := (cech f).obj (op (SimplexCategory.mk k))
  have evaluate (s : (free R).obj P ⟶ F) (U : Scheme.{0}) (v : P.obj (op U)) :
      val s U v =
        ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom).app (op U)).hom
          (ModuleCat.freeMk (ULift.up v)) := rfl
  have hext (s s' : (free R).obj P ⟶ F) (hs : ∀ U v, val s U v = val s' U v) : s = s' := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ F.property
    apply NatTrans.ext
    funext U
    apply ModuleCat.free_hom_ext
    rintro ⟨v⟩
    have hv := hs U.unop v
    rw [evaluate, evaluate] at hv
    exact hv
  have hex (φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
      (hφ : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : P.obj (op U)),
        φ V (P.map g.op v) = Sec.res g (φ U v)) :
      ∃ s : (free R).obj P ⟶ F, ∀ U v, val s U v = φ U v := by
    let s := GlobalTheory.EtC.FreeHom.desc P F φ hφ
    refine ⟨s, ?_⟩
    intro U v
    rw [evaluate]
    have hdesc : toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom =
        GlobalTheory.EtC.FreeHom.descP P F φ hφ := by
      have h := ((sheafificationAdjunction Scheme.etaleTopology.{0}
        (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).apply_symm_apply
          (GlobalTheory.EtC.FreeHom.descP P F φ hφ)
      rw [Adjunction.homEquiv_unit] at h
      exact h
    rw [hdesc]
    change (ModuleCat.freeDesc _).hom (ModuleCat.freeMk (ULift.up v)) = _
    erw [ModuleCat.freeDesc_apply]
    rfl
  have hnat (s : (free R).obj P ⟶ F) (V U : Scheme.{0}) (g : V ⟶ U) (v : P.obj (op U)) :
      val s V (P.map g.op v) = Sec.res g (val s U v) := by
    rw [evaluate, evaluate]
    let η := toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom
    change (η.app (op V)).hom (ModuleCat.freeMk (ULift.up (P.map g.op v))) =
      (F.obj.map g.op).hom ((η.app (op U)).hom (ModuleCat.freeMk (ULift.up v)))
    rw [← GlobalTheory.EtC.FreeHom.freePresheaf_map_freeMk P g.op v]
    exact congrArg (fun m => m.hom (ModuleCat.freeMk (ULift.up v))) (η.naturality g.op)
  constructor
  · intro s s' hs
    change val s Z (cechPt f k x y h) = val s' Z (cechPt f k x y h) at hs
    apply hext
    intro U v
    obtain ⟨g, rfl⟩ := (e U).2 v
    dsimp only
    rw [hnat s U Z g, hnat s' U Z g, hs]
  · intro a
    choose c hc0 using fun (U : Scheme.{0}) (v : ((cech f).obj (op (SimplexCategory.mk k))).obj (op U)) => (e U).2 v
    have hc' : ∀ (U : Scheme.{0}) (v : ((cech f).obj (op (SimplexCategory.mk k))).obj (op U)),
        ((cech f).obj (op (SimplexCategory.mk k))).map (c U v).op (cechPt f k x y h) = v := hc0
    obtain ⟨s, hs⟩ := hex (fun U v => Sec.res (c U v) a) (by
      intro V U g v
      have h1 : c V (((cech f).obj (op (SimplexCategory.mk k))).map g.op v) = g ≫ c U v := by
        apply (e V).1
        change ((cech f).obj (op (SimplexCategory.mk k))).map (c V _).op (cechPt f k x y h) =
          ((cech f).obj (op (SimplexCategory.mk k))).map (g ≫ c U v).op (cechPt f k x y h)
        rw [hc' V, op_comp, Functor.map_comp_apply, hc' U v]
      dsimp only
      rw [h1]
      simp [Sec.res])
    refine ⟨s, ?_⟩
    change val s Z (cechPt f k x y h) = a
    rw [hs]
    have h2 : c Z (cechPt f k x y h) = 𝟙 Z := by
      apply (e Z).1
      change ((cech f).obj (op (SimplexCategory.mk k))).map (c Z _).op (cechPt f k x y h) =
        ((cech f).obj (op (SimplexCategory.mk k))).map (𝟙 Z).op (cechPt f k x y h)
      rw [hc' Z, op_id, P.map_id]
      exact (types_id_apply (P.obj (op Z)) (cechPt f k x y h)).symm
    rw [h2]
    simp [Sec.res]
