module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains

@[expose] public section

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
open scoped Simplicial
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.EZ.Cone

theorem homExt {m a : ℕ} {f g : ⦋m⦌ ⟶ ⦋a⦌}
    (h : ∀ j : Fin (m + 1), (f.toOrderHom j : ℕ) = g.toOrderHom j) : f = g :=
  SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun j => Fin.ext (h j)))

def cv {n a : ℕ} (f : ⦋n⦌ ⟶ ⦋a⦌) : ⦋n + 1⦌ ⟶ ⦋a⦌ :=
  SimplexCategory.mkHom ⟨fun j => if h : (j : ℕ) = 0 then 0 else
      f.toOrderHom ⟨(j : ℕ) - 1, by have := j.2; change _ < n + 1; omega⟩, by
    intro i j hij
    have hij' : (i : ℕ) ≤ j := hij
    dsimp only
    split_ifs with hi hj hj
    · exact le_refl _
    · exact Fin.zero_le _
    · omega
    · exact f.toOrderHom.monotone (show ((⟨(i : ℕ) - 1, _⟩ : Fin _) ≤ ⟨(j : ℕ) - 1, _⟩) from by
        rw [Fin.mk_le_mk]; omega)⟩

theorem cv_apply {n a : ℕ} (f : ⦋n⦌ ⟶ ⦋a⦌) (j : Fin (n + 2)) :
    ((cv f).toOrderHom j : ℕ) = if h : (j : ℕ) = 0 then 0 else
      (f.toOrderHom ⟨(j : ℕ) - 1, by have := j.2; change _ < n + 1; omega⟩ : ℕ) := by
  simp only [cv, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk]
  split_ifs <;> rfl

theorem fc_apply (n m i : ℕ) (j : Fin (m + 1)) :
    ((fc n m i).toOrderHom j : ℕ) = min n (faceFun i j) := rfl

theorem idc_apply (n m : ℕ) (j : Fin (m + 1)) :
    ((idc n m).toOrderHom j : ℕ) = min n j := rfl

theorem face_cone_identity_zero {m a : ℕ} (f : ⦋m⦌ ⟶ ⦋a⦌) : fc (m + 1) m 0 ≫ cv f = f := by
  apply homExt; intro j
  rw [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, cv_apply]
  have h1 : ((fc (m + 1) m 0).toOrderHom j : ℕ) = j + 1 := by
    rw [fc_apply]; unfold faceFun; have := j.2; split_ifs <;> omega
  rw [dite_eq_right (by omega)]
  congr 2; apply Fin.ext; simp only [h1]; omega

theorem fcs_cv {m a : ℕ} (f : ⦋m + 1⦌ ⟶ ⦋a⦌) (k : ℕ) :
    fc (m + 2) (m + 1) (k + 1) ≫ cv f = cv (fc (m + 1) m k ≫ f) := by
  apply homExt; intro j
  rw [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, cv_apply, cv_apply]
  have hj := j.2
  by_cases h0 : (j : ℕ) = 0
  · rw [dite_eq_left h0]
    have : ((fc (m + 2) (m + 1) (k + 1)).toOrderHom j : ℕ) = 0 := by
      rw [fc_apply]; unfold faceFun; split_ifs <;> omega
    rw [dite_eq_left this]
  · have h1 : ((fc (m + 2) (m + 1) (k + 1)).toOrderHom j : ℕ) ≠ 0 := by
      rw [fc_apply]; unfold faceFun; split_ifs <;> omega
    rw [dite_eq_right h1, dite_eq_right h0, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
    congr 2; apply Fin.ext
    simp only [fc_apply]; unfold faceFun; split_ifs <;> omega

theorem face_cone_identity_one {a : ℕ} (f : ⦋0⦌ ⟶ ⦋a⦌) : fc 1 0 1 ≫ cv f = idc a 0 := by
  apply homExt; intro j
  rw [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, cv_apply, idc_apply]
  have hj := j.2
  have : ((fc 1 0 1).toOrderHom j : ℕ) = 0 := by
    rw [fc_apply]; unfold faceFun; split_ifs <;> omega
  rw [dite_eq_left this]; omega

theorem bop_comp {n m p q r s : ℕ} (α : ⦋p⦌ ⟶ ⦋n⦌) (β : ⦋q⦌ ⟶ ⦋m⦌) (α' : ⦋r⦌ ⟶ ⦋p⦌)
    (β' : ⦋s⦌ ⟶ ⦋q⦌) : bop α β ≫ bop α' β' = bop (α' ≫ α) (β' ≫ β) := by
  have h := Free.single_comp_single ℤ (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ)
    (show (op ⦋n⦌, op ⦋m⦌) ⟶ (op ⦋p⦌, op ⦋q⦌) from (α.op, β.op))
    (show (op ⦋p⦌, op ⦋q⦌) ⟶ (op ⦋r⦌, op ⦋s⦌) from (α'.op, β'.op)) 1 1
  rw [mul_one] at h
  exact h

def coneHom {a b n : ℕ} (x : (op ⦋a⦌, op ⦋b⦌) ⟶ (op ⦋n⦌, op ⦋n⦌)) :
    (op ⦋a⦌, op ⦋b⦌) ⟶ (op ⦋n + 1⦌, op ⦋n + 1⦌) :=
  ((cv x.1.unop).op, (cv x.2.unop).op)

def cone (a b n : ℕ) : (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1)) :=
  Finsupp.mapDomain.addMonoidHom coneHom

def eps (a b : ℕ) : (bo a b ⟶ bo 0 0) →+ ℤ := Finsupp.liftAddHom (fun _ => AddMonoidHom.id ℤ)

theorem cone_bop {a b n : ℕ} (α : ⦋n⦌ ⟶ ⦋a⦌) (β : ⦋n⦌ ⟶ ⦋b⦌) :
    cone a b n (bop α β) = bop (cv α) (cv β) := by
  exact Finsupp.mapDomain_single

theorem eps_bop {a b : ℕ} (α : ⦋0⦌ ⟶ ⦋a⦌) (β : ⦋0⦌ ⟶ ⦋b⦌) : eps a b (bop α β) = 1 := by
  exact Finsupp.liftAddHom_apply_single _ _ _

theorem single_eq {a b n p : ℕ} (x : (op ⦋a⦌, op ⦋b⦌) ⟶ (op ⦋n⦌, op ⦋p⦌)) (c : ℤ) :
    (Finsupp.single x c : bo a b ⟶ bo n p) = c • bop x.1.unop x.2.unop := by
  have h := map_zsmul (Finsupp.singleAddHom (M := ℤ) x) c (1 : ℤ)
  rw [smul_eq_mul, mul_one] at h
  exact h

theorem ind {a b n p : ℕ} (P : (bo a b ⟶ bo n p) → Prop) (h0 : P 0) (hadd : ∀ f g, P f → P g → P (f + g))
    (hs : ∀ (α : ⦋n⦌ ⟶ ⦋a⦌) (β : ⦋p⦌ ⟶ ⦋b⦌) (c : ℤ), P (c • bop α β)) (r : bo a b ⟶ bo n p) : P r :=
  Finsupp.induction_linear r h0 hadd (fun x c => by have h := hs x.1.unop x.2.unop c; rw [← single_eq] at h; exact h)

theorem key {a b n : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋a⦌) (β : ⦋n + 1⦌ ⟶ ⦋b⦌) :
    cone a b (n + 1) (bop α β) ≫ dD (n + 2) (n + 1) = bop α β - cone a b n (bop α β ≫ dD (n + 1) n) := by
  rw [cone_bop]
  unfold dD
  rw [ite_eq_left rfl, ite_eq_left rfl]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, bop_comp, map_sum, map_zsmul, cone_bop]
  rw [Finset.sum_range_succ' _ (n + 2)]
  have h0 : fc (n + 2) (n + 1) 0 ≫ cv α = α := face_cone_identity_zero α
  have h0' : fc (n + 2) (n + 1) 0 ≫ cv β = β := face_cone_identity_zero β
  simp only [h0, h0', fcs_cv, pow_succ, pow_zero, one_smul, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib]
  abel

theorem key0 {a b : ℕ} (α : ⦋0⦌ ⟶ ⦋a⦌) (β : ⦋0⦌ ⟶ ⦋b⦌) :
    cone a b 0 (bop α β) ≫ dD 1 0 = bop α β - bop (idc a 0) (idc b 0) := by
  rw [cone_bop]
  unfold dD
  rw [ite_eq_left rfl]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, bop_comp]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, face_cone_identity_one]
  have h0 : fc 1 0 0 ≫ cv α = α := face_cone_identity_zero α
  have h0' : fc 1 0 0 ≫ cv β = β := face_cone_identity_zero β
  simp only [h0, h0', pow_zero, pow_one, one_smul, neg_smul, zero_add]
  abel

theorem coneContraction : ∃ (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1)))
    (ε : ∀ a b : ℕ, (bo a b ⟶ bo 0 0) →+ ℤ),
    (∀ (a b : ℕ) (α : SimplexCategory.mk 0 ⟶ SimplexCategory.mk a) (β : SimplexCategory.mk 0 ⟶ SimplexCategory.mk b),
      ε a b (bop α β) = 1) ∧
    (∀ (a b : ℕ) (r : bo a b ⟶ bo 0 0), cone a b 0 r ≫ dD 1 0 = r - ε a b r • bop (idc a 0) (idc b 0)) ∧
    ∀ (a b n : ℕ) (r : bo a b ⟶ bo (n + 1) (n + 1)),
      cone a b (n + 1) r ≫ dD (n + 2) (n + 1) = r - cone a b n (r ≫ dD (n + 1) n) := by
  refine ⟨cone, eps, fun a b α β => eps_bop α β, ?_, ?_⟩
  · intro a b r
    refine ind (P := fun r => cone a b 0 r ≫ dD 1 0 = r - eps a b r • bop (idc a 0) (idc b 0)) ?_ ?_ ?_ r
    · rw [map_zero, map_zero, Limits.zero_comp, zero_smul, sub_zero]
    · intro f g hf hg
      simp only [map_add (f := _), Preadditive.add_comp, add_smul, hf, hg]
      abel
    · intro α β c
      rw [map_zsmul, Preadditive.zsmul_comp, key0, map_zsmul, eps_bop, smul_sub, smul_eq_mul, mul_one]
  · intro a b n r
    refine ind (P := fun r => cone a b (n + 1) r ≫ dD (n + 2) (n + 1) = r - cone a b n (r ≫ dD (n + 1) n))
      ?_ ?_ ?_ r
    · rw [map_zero, Limits.zero_comp, Limits.zero_comp, map_zero, sub_zero]
    · intro f g hf hg
      simp only [map_add (f := _), Preadditive.add_comp, hf, hg]
      abel
    · intro α β c
      rw [map_zsmul, Preadditive.zsmul_comp, key, Preadditive.zsmul_comp, map_zsmul, smul_sub]

end GlobalTheory.EZ.Cone
