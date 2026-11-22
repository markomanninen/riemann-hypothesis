module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleLiftingLineBundleTransitionUnits
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwZ
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneralLinearGroupDetMapFinOne

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cocycle_lifting_lineBundle_transition_units : ∀ (q : ℕ) (C : Shv ℤ) (qb : C ⟶ Gm) (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → (∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U))) → ∃ a : Cocycle ((chains ℤ).obj E) (sgl C) 1, ∀ (U : Scheme.{0}) (x : Sx E 1 U), ∃ c : Sec C U, Sec.map qb c = unitSec (lineUnit L x) ∧ ev a.1 1 0 (by simp) U x = Sec.map (sglι C) c := by
  intro q C qb E L hE hb
  obtain ⟨α, hα⟩ := CupSpec.ev_exists (liftFam qb L hE hb) (liftFam_nat qb L hE hb)
  have hδα : δ 1 2 α = 0 := by
    apply CupSpec.ev_ext
    intro p t ht U x
    rw [CupSpec.ev_zero]
    by_cases h0 : t = 0
    · subst h0
      obtain rfl : p = 2 := by omega
      rw [CupSpec.ev_δ_succ (by norm_num) α U 1 (-1) 0 (by simp) ht x]
      simp only [hα]
      rw [show liftFam qb L hE hb 2 (-1) (by simp) U x = 0 from rfl,
        PicSpec.sec_map_zero, zero_add, Fin.sum_univ_three]
      simp only [liftFam_one]
      rw [liftSec_face, PicSpec.sec_map_add]
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
      simp
    · exact PicSpec.sec_eq_zero (HomologicalComplex.isZero_single_obj_X _ _ _ _ h0) _
  refine ⟨Cocycle.mk α 2 (by norm_num) hδα, fun U x =>
    ⟨liftSec qb L hE hb U x, liftSec_spec qb L hE hb U x, ?_⟩⟩
  exact (hα 1 0 _ U x).trans (liftFam_one qb L hE hb _ U x)
