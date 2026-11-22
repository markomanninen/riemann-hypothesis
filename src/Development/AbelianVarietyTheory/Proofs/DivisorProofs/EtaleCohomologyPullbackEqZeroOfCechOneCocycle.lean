module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicPropertiesStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

noncomputable section

namespace GlobalTheory.CechOne

def cechDiag {Y X : Scheme.{0}} (f : Y ⟶ X) : sch.obj Y ⟶ cech f where
  app n := WidePullback.lift (arrows := fun _ : Fin (n.unop.len + 1) => yoneda.map f) (yoneda.map f)
    (fun _ => 𝟙 (yoneda.obj Y)) (fun _ => Category.id_comp _)
  naturality m n g := by
    apply WidePullback.hom_ext
    · intro j
      simp only [cech, Arrow.cechNerve]
      erw [Category.assoc, Category.assoc, WidePullback.lift_π, WidePullback.lift_π, WidePullback.lift_π]
      rfl
    · simp only [cech, Arrow.cechNerve]
      erw [Category.assoc, Category.assoc, WidePullback.lift_base, WidePullback.lift_base, WidePullback.lift_base]
      rfl

theorem cechDiag_aug {Y X : Scheme.{0}} (f : Y ⟶ X) : cechDiag f ≫ cechAug f = sch.map f := by
  ext n : 1
  simp only [cechDiag, cechAug]
  erw [NatTrans.comp_app, Arrow.augmentedCechNerve_hom_app, WidePullback.lift_base]
  rfl

theorem isCls_zero_deg_one (R : Type) [CommRing R] (F : Shv R) (E : Spc) :
    IsCls (R := R) (E := E) (n := 1) (0 : (free R).obj (E.obj (op ⦋1⦌)) ⟶ F)
      (0 : H R E F ((1 : ℕ) : ℤ)) := by
  refine ⟨0, ?_, ?_⟩ <;> simp

theorem cechDiag_δ {Y X : Scheme.{0}} (f : Y ⟶ X) (i : Fin 3) :
    (cechDiag f).app (op ⦋2⦌) ≫ SimplicialObject.δ (cech f) i = (cechDiag f).app (op ⦋1⦌) := by
  rw [SimplicialObject.δ, ← NatTrans.naturality]
  simp [sch, disc]

theorem pull_sch_eq_zero (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (f : Y ⟶ X)
    (s : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ F)
    (hs : cobd (R := R) (E := cech f) (n := 1) s = 0)
    (x : H R (sch.obj X) F ((1 : ℕ) : ℤ))
    (hx : IsCls (R := R) (E := cech f) (n := 1) s (pull R (cechAug f) F ((1 : ℕ) : ℤ) x)) :
    pull R (sch.map f) F ((1 : ℕ) : ℤ) x = 0 := by
  have hc := congrArg (fun t => (free R).map ((cechDiag f).app (op ⦋2⦌)) ≫ t) hs
  simp only [cobd, Preadditive.comp_sum, Preadditive.comp_zsmul, ← Functor.map_comp_assoc, cechDiag_δ,
    comp_zero] at hc
  have hc' : ((free R).map ((cechDiag f).app (op ⦋1⦌)) ≫ s : (free R).obj ((sch.obj Y).obj (op ⦋2⦌)) ⟶ F) = 0 := by
    simpa [Fin.sum_univ_succ] using hc
  have hd : (free R).map ((cechDiag f).app (op ⦋1⦌)) ≫ s = 0 := hc'
  have h0 : pull R (cechDiag f) F ((1 : ℕ) : ℤ) (pull R (cechAug f) F ((1 : ℕ) : ℤ) x) = 0 := by
    obtain ⟨z, hzClass, hz⟩ := hx
    rw [← hzClass]
    simp only [pull, HK.pull, HK.pre, cpre_mk]
    rw [← CohomologyClass.mk_zero]
    apply congrArg CohomologyClass.mk
    apply Cocycle.ext
    change (Cochain.ofHom ((chains R).map (cechDiag f))).comp z.1 (zero_add _) = 0
    rw [hz, ClsBasic.ofHom_comp_single]
    simp only [← Category.assoc, ClsBasic.chainsXIso_nat]
    simp [Category.assoc, hd]
  rw [← cechDiag_aug f, pull_comp]
  exact h0

end GlobalTheory.CechOne

end
