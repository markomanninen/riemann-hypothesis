module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwZ
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneralLinearGroupDetMapFinOne

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.EtC.KumPic.PostVal

theorem ev_comp_ofHom {E : Spc} {I J : Cx ℤ} {n : ℤ} (α : Cochain ((chains ℤ).obj E) I n) (m : I ⟶ J)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  unfold ev
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

theorem sglι_resAug (C : Shv ℤ) : sglι C ≫ (resAug C).f 0 = resι ℤ C := rfl

theorem resι_resMap {C G : Shv ℤ} (φ : C ⟶ G) : resι ℤ C ≫ (resMap ℤ φ).f 0 = φ ≫ resι ℤ G := by
  unfold resι resMap res
  rw [InjectiveResolution.ι'_f_zero, InjectiveResolution.ι'_f_zero,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) (i' := 0) (by simp)]
  simp [InjectiveResolution.cochainComplexXIso]

theorem post_eq_picClass (C : Shv ℤ) (qb : C ⟶ Gm) (E : Spc) (L : E ⟶ ofCat (glCat 1))
    (a : Cocycle ((chains ℤ).obj E) (sgl C) 1)
    (ha : ∀ (U : Scheme.{0}) (x : Sx E 1 U), ∃ c : Sec C U, Sec.map qb c = unitSec (lineUnit L x) ∧
      ev a.1 1 0 (by simp) U x = Sec.map (sglι C) c) :
    HK.post ℤ _ qb 1 (CohomologyClass.mk (zcomp a (Cocycle.ofHom (resAug C)) (add_zero 1))) = picClass L := by
  let β := zcomp (zcomp a (Cocycle.ofHom (resAug C)) (add_zero 1))
    (Cocycle.ofHom (resMap ℤ qb)) (add_zero 1)
  change CohomologyClass.mk β = picClass L
  have hβ₀ (U : Scheme.{0}) (x : Sx E 0 U) : ev β.1 0 1 (by simp) U x = 0 := by
    change ev ((a.1.comp (Cochain.ofHom (resAug C)) (add_zero 1)).comp
      (Cochain.ofHom (resMap ℤ qb)) (add_zero 1))
      0 1 _ U x = 0
    rw [ev_comp_ofHom, ev_comp_ofHom,
      GlobalTheory.EtC.PicSpec.sec_eq_zero (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by decide)) (ev a.1 0 1 _ U x),
      GlobalTheory.EtC.PicSpec.sec_map_zero, GlobalTheory.EtC.PicSpec.sec_map_zero]
  have hβ₁ (U : Scheme.{0}) (x : Sx E 1 U) :
      ev β.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)) := by
    obtain ⟨c, hc, hv⟩ := ha U x
    change ev ((a.1.comp (Cochain.ofHom (resAug C)) (add_zero 1)).comp
      (Cochain.ofHom (resMap ℤ qb)) (add_zero 1))
      1 0 _ U x = _
    rw [ev_comp_ofHom, ev_comp_ofHom, hv, GlobalTheory.EtC.PicSpec.sec_map_comp, GlobalTheory.EtC.PicSpec.sec_map_comp, ← hc,
      GlobalTheory.EtC.PicSpec.sec_map_comp, ← Category.assoc, sglι_resAug, resι_resMap]
  let P (c : H ℤ E Gm 1) : Prop :=
    ∃ γ : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1, CohomologyClass.mk γ = c ∧
      (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : Sx E 1 U),
        ev γ.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x))
  have hspec : P (picClass L) := by
    change P (pick P)
    exact pick_spec ⟨_, β, rfl, hβ₀, hβ₁⟩
  obtain ⟨γ, hγ, hγ₀, hγ₁⟩ := hspec
  have hEq : β = γ := by
    refine Cocycle.ext (CupSpec.ev_ext β.1 γ.1 fun p s h U x => ?_)
    match p with
    | 0 =>
      obtain rfl : s = 1 := by omega
      exact (hβ₀ U x).trans (hγ₀ U x).symm
    | 1 =>
      obtain rfl : s = 0 := by omega
      exact (hβ₁ U x).trans (hγ₁ U x).symm
    | p + 2 =>
      have hZ := GlobalTheory.EtC.PicSpec.res_isZero Gm s (by omega)
      exact (GlobalTheory.EtC.PicSpec.sec_eq_zero hZ _).trans
        (GlobalTheory.EtC.PicSpec.sec_eq_zero hZ _).symm
  rw [hEq, hγ]

end GlobalTheory.EtC.KumPic.PostVal
