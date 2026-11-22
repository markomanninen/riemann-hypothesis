module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.Liouville

@[expose] public section

open Complex Metric

noncomputable section

namespace Formalism.ZF

lemma zflb_exists_log {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (ball z₀ R)) (hne : ∀ z ∈ ball z₀ R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, g z₀ = 0 ∧ (∀ z ∈ ball z₀ R, HasDerivAt g (deriv f z / f z) z) ∧
      ∀ z ∈ ball z₀ R, f z = f z₀ * Complex.exp (g z) := by
  obtain ⟨g, hg₀, hg⟩ := ((hf.deriv isOpen_ball).div hf hne).isExactOn_ball.with_val_at z₀ 0
  refine ⟨g, hg₀, hg, ?_⟩
  have hd : DifferentiableOn ℂ g (ball z₀ R) :=
    fun z hz => (hg z hz).differentiableAt.differentiableWithinAt
  obtain ⟨c, _, hc⟩ := (logDeriv_eqOn_iff hf hd.cexp isOpen_ball isPreconnected_ball
    (fun _ _ => Complex.exp_ne_zero _) hne).mp fun z hz => by
      simp [logDeriv_apply, (hg z hz).cexp.deriv]
  intro z hz
  have hcenter := hc (mem_ball_self (pos_of_mem_ball hz))
  have hfc : f z₀ = c := by simpa [hg₀] using hcenter
  simpa [hfc] using hc hz

theorem logDerivBoundOnBall : LogDerivBound := by
  intro f z₀ R M hR hM hf hne hbd z hz
  have hR0 : R ≠ 0 := hR.ne'
  have hfb : DifferentiableOn ℂ f (ball z₀ R) := hf.mono ball_subset_closedBall
  have hneb : ∀ w ∈ ball z₀ R, f w ≠ 0 := fun w hw => hne w (ball_subset_closedBall hw)
  obtain ⟨g, hg0, hgd, hgf⟩ := zflb_exists_log hfb hneb
  have hf0 : 0 < ‖f z₀‖ := norm_pos_iff.2 (hne z₀ (mem_closedBall_self hR.le))
  have hre : ∀ w ∈ ball z₀ R, (g w).re ≤ Real.log M := by
    intro w hw
    have h1 := hbd w (ball_subset_closedBall hw)
    rw [hgf w hw, norm_mul, Complex.norm_exp] at h1
    exact (Real.le_log_iff_exp_le (lt_of_lt_of_le zero_lt_one hM)).2
      ((mul_le_mul_iff_right₀ hf0).mp (by simpa only [mul_comm M] using h1))
  have hzb : dist z z₀ ≤ R / 2 := hz
  have hshift : ∀ v ∈ ball (0 : ℂ) R, z₀ + v ∈ ball z₀ R := by
    intro v hv
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact mem_ball_zero_iff.1 hv
  have hmain : ∀ A : ℝ, Real.log M < A → ‖deriv f z / f z‖ ≤ 24 * A / R := by
    intro A hA
    have hA0 : 0 < A := lt_of_le_of_lt (Real.log_nonneg hM) hA
    have hhd : DifferentiableOn ℂ (fun v => g (z₀ + v)) (ball 0 R) := by
      intro v hv
      exact ((hgd _ (hshift v hv)).differentiableAt.comp v
        (differentiableAt_id.const_add z₀)).differentiableWithinAt
    have hhm : Set.MapsTo (fun v => g (z₀ + v)) (ball 0 R) {w | w.re ≤ A} := by
      intro v hv
      exact le_trans (hre _ (hshift v hv)) hA.le
    have hbc : ∀ w ∈ closedBall z₀ (3 * R / 4), ‖g w‖ ≤ 6 * A := by
      intro w hw
      obtain ⟨u, rfl⟩ : ∃ u, w = z₀ + u := ⟨w - z₀, by ring⟩
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left] at hw
      have huR : u ∈ ball (0 : ℂ) R := by
        rw [mem_ball_zero_iff]
        linarith
      have hB : ‖g (z₀ + u)‖ ≤ 2 * A * ‖u‖ / (R - ‖u‖) :=
        Complex.borelCaratheodory_zero hA0 hhd hhm hR huR (by simpa using hg0)
      have hpos : 0 < R - ‖u‖ := by linarith
      calc ‖g (z₀ + u)‖ ≤ 2 * A * ‖u‖ / (R - ‖u‖) := hB
        _ ≤ 6 * A := by
          rw [div_le_iff₀ hpos]
          nlinarith [norm_nonneg u]
    have hR4 : 0 < R / 4 := by linarith
    have hsub : closedBall z (R / 4) ⊆ ball z₀ R := by
      intro w hw
      rw [mem_closedBall] at hw
      rw [mem_ball]
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ < R := by linarith
    have hdiff : DiffContOnCl ℂ g (ball z (R / 4)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball z hR4.ne']
      intro w hw
      exact (hgd w (hsub hw)).differentiableAt.differentiableWithinAt
    have hC : ∀ w ∈ sphere z (R / 4), ‖g w‖ ≤ 6 * A := by
      intro w hw
      apply hbc
      rw [mem_sphere] at hw
      rw [mem_closedBall]
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ ≤ 3 * R / 4 := by linarith
    have hzb' : z ∈ ball z₀ R := hsub (mem_closedBall_self hR4.le)
    have hder := norm_deriv_le_of_forall_mem_sphere_norm_le hR4 hdiff hC
    rw [(hgd z hzb').deriv] at hder
    calc ‖deriv f z / f z‖ ≤ 6 * A / (R / 4) := hder
      _ = 24 * A / R := by
        field_simp
        all_goals ring
  apply le_of_forall_pos_le_add
  intro ε hε
  have hεR : 0 < ε * R / 24 := by positivity
  have h := hmain (Real.log M + ε * R / 24) (by linarith)
  calc ‖deriv f z / f z‖ ≤ 24 * (Real.log M + ε * R / 24) / R := h
    _ = 24 * Real.log M / R + ε := by
      field_simp

end Formalism.ZF
