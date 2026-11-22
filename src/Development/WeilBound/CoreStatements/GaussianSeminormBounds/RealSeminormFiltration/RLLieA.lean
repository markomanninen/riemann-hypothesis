module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

@[expose] public section

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix Filter Topology Asymptotics
open scoped Real RealInnerProductSpace ContDiff

namespace PositivityTheory.RL.Up

open GlobalTheory.RealWeil

theorem bdd_of_weak {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (h : ℝ → B)
    (hc : ∀ φ : B →L[ℂ] ℂ, Continuous fun t => φ (h t)) : ∃ M, ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖h t‖ ≤ M := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun t : Set.Icc (-1 : ℝ) 1 => NormedSpace.inclusionInDoubleDual ℂ B (h t))
    fun φ => by
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc φ).continuousOn
      exact ⟨C, fun t => hC t t.2⟩
  refine ⟨C, fun t ht => ?_⟩
  have := hC ⟨t, ht⟩
  rwa [show ‖NormedSpace.inclusionInDoubleDual ℂ B (h t)‖ = ‖h t‖ from
    (NormedSpace.inclusionInDoubleDualLi ℂ (E := B)).norm_map (h t)] at this

theorem taylor2 (φ φ' φ'' : ℝ → ℂ) (h1 : ∀ t, HasDerivAt φ (φ' t) t) (h2 : ∀ t, HasDerivAt φ' (φ'' t) t) {M : ℝ}
    (hM : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖φ'' t‖ ≤ M) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    ‖φ t - φ 0 - t * φ' 0‖ ≤ M * t ^ 2 := by
  have h0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 h0)
  have a1 : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ‖φ' u - φ' 0‖ ≤ M * ‖u - 0‖ := fun u hu =>
    (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le (fun x _ => (h2 x).hasDerivWithinAt) hM h0 hu
  have hsub : Set.uIcc 0 t ⊆ Set.Icc (-1 : ℝ) 1 := Set.uIcc_subset_Icc h0 ht
  have a2 := (convex_uIcc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u : ℝ => φ u - u * φ' 0) (f' := fun u => φ' u - φ' 0) (C := M * |t|)
    (fun x _ => ((h1 x).sub ((((hasDerivAt_id x).ofReal_comp).mul_const (φ' 0)).congr_deriv (by simp))).hasDerivWithinAt)
    (fun u hu => (a1 u (hsub hu)).trans (by
      rw [sub_zero, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (by simpa using Set.abs_sub_left_of_mem_uIcc hu) hM0))
    Set.left_mem_uIcc Set.right_mem_uIcc
  rw [sub_zero, Real.norm_eq_abs, mul_assoc, abs_mul_abs_self, ← sq] at a2
  refine le_trans (le_of_eq (congrArg norm ?_)) a2
  push_cast
  ring

variable {l : Type} [Fintype l] [DecidableEq l]


end PositivityTheory.RL.Up

end
