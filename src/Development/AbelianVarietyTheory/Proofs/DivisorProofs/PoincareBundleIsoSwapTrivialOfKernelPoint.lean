module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AbLaw GlobalTheory.CechPic

namespace GlobalTheory.AbDual

theorem lbIso_swap_and_triv_of_ker : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (P₀ : LB (A ⊗ B).left), GlobalTheory.AbDual.IsDual A B P₀ → ∀ (P : LB (A ⊗ A).left), P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∀ (l : A ⟶ B), LBIso P (GlobalTheory.AbDual.ev P₀ (fst A A) (snd A A ≫ l)) → LBIso (GlobalTheory.AbDual.ev P (fst A A) (snd A A ≫ 𝟙 A)) (GlobalTheory.AbDual.ev (GlobalTheory.AbDual.swap P₀) (fst A A ≫ l) (snd A A)) ∧ ∀ (T : Over (Sp k)) (x : T ⟶ A), x ≫ l = 1 → ∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen := by
  intro k _ A B _ _ P₀ hD P hP hsym l hl
  have hP₀ := hD.isLB
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → (F : Y ⟶ X) → (L.pull F).IsLB := by
    intro X Y L hL F
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  have pullIso : ∀ {X Y Z : Scheme.{0}} {M : LB Y} {N : LB X} {f : Y ⟶ X},
      LBIso M (N.pull f) → (g : Z ⟶ Y) → LBIso (M.pull g) (N.pull (g ≫ f)) := by
    intro X Y Z M N f H g
    exact H.chartPull (chartPullPull M g)
      (chartPullSame N (fun _ : PUnit => g ≫ f) (fun _ : PUnit => f) (fun _ => 1) g fun _ => rfl)
  have key : ∀ (Y : Over (Sp k)) (a b : Y ⟶ A), LBIso (ev P a b) (ev P₀ b (a ≫ l)) := by
    intro Y a b
    have hs := pullIso hsym (lift a b).left
    have hl' := pullIso hl (lift b a).left
    have es : LBIso (ev P a b) (ev P b a) := by
      simpa only [← Over.comp_left, comp_lift, lift_snd, lift_fst] using hs
    have el : LBIso (ev P b a) (ev P₀ b (a ≫ l)) := by
      simpa only [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc] using hl'
    exact (CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP₀ _)).1
      (((CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP _)).2 es).trans
       ((CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP₀ _)).2 el))
  refine ⟨?_, fun T x hx => ?_⟩
  · have hs : LBIso (swap P₀) (swap P₀) := (CechPic.cls_eq_iff (pull_isLB hP₀ _) (pull_isLB hP₀ _)).1 rfl
    have hs' := pullIso hs (lift (fst A A ≫ l) (snd A A)).left
    have hs'' : LBIso (ev (swap P₀) (fst A A ≫ l) (snd A A)) (ev P₀ (snd A A) (fst A A ≫ l)) := by
      simpa only [swap, ev, ← Over.comp_left, comp_lift, lift_fst, lift_snd] using hs'
    apply (CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB (pull_isLB hP₀ _) _)).1
    exact ((CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP₀ _)).2 (by simpa only [Category.comp_id] using key (A ⊗ A) (fst A A) (snd A A))).trans
      ((CechPic.cls_eq_iff (pull_isLB (pull_isLB hP₀ _) _) (pull_isLB hP₀ _)).2 hs'').symm
  · have hk := key (A ⊗ T) (snd A T ≫ x) (fst A T)
    simp only [Category.assoc, hx, MonObj.comp_one] at hk
    have ht : Triv (ev P₀ (fst A T) (1 : A ⊗ T ⟶ B)) := by
      obtain ⟨t, ht⟩ := hD.zero
      have h := DVR.pullGen_isGen _ _ _ t ht (fst A T).left
      simpa only [ev, ← Over.comp_left, comp_lift, Category.comp_id, MonObj.comp_one] using (show Triv _ from ⟨_, h⟩)
    exact (CechPic.iso_triv_iff _).1 ((CechPic.cls_eq_iff (LB.isLB_triv _) (pull_isLB hP _)).1
      (((CechPic.cls_eq_iff (LB.isLB_triv _) (pull_isLB hP₀ _)).2 ((CechPic.iso_triv_iff _).2 ht)).trans
        ((CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP₀ _)).2 hk).symm))

end GlobalTheory.AbDual
