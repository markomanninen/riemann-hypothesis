module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCut

@[expose] public section

open Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVCrdGerm

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutMP

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {r : ℕ}

theorem pbOp_germ (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    pbOp l f₁ =ᶠ[𝓝 c] pbOp l f₂ := by
  filter_upwards [h.eventuallyEq_nhds] with c' hc'
  simp only [pbOp, wirtBar, hc'.fderiv_eq]

theorem cbOp_germ (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    cbOp l f₁ =ᶠ[𝓝 c] cbOp l f₂ := by
  filter_upwards [h] with c' hc'
  simp only [cbOp, hc']

theorem cbiOp_germ (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    cbiOp l f₁ =ᶠ[𝓝 c] cbiOp l f₂ := by
  filter_upwards [h] with c' hc'
  simp only [cbiOp, hc']

theorem pbN_germ (i : ℕ) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    pbN r i f₁ =ᶠ[𝓝 c] pbN r i f₂ := by
  unfold pbN
  split_ifs with hi
  · exact pbOp_germ _ h
  · exact EventuallyEq.rfl

theorem cbN_germ (i : ℕ) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    cbN r i f₁ =ᶠ[𝓝 c] cbN r i f₂ := by
  unfold cbN
  split_ifs with hi
  · exact cbOp_germ _ h
  · exact EventuallyEq.rfl

theorem cbiN_germ (i : ℕ) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    cbiN r i f₁ =ᶠ[𝓝 c] cbiN r i f₂ := by
  unfold cbiN
  split_ifs with hi
  · exact cbiOp_germ _ h
  · exact EventuallyEq.rfl

theorem iteratedOperator_germ (w : ℂ) : ∀ (m : ℕ) (f₁ f₂ : (Fin r → ℂ) → X) (c : Fin r → ℂ), f₁ =ᶠ[𝓝 c] f₂ →
    (kvP r w m).1 f₁ =ᶠ[𝓝 c] (kvP r w m).1 f₂ ∧ (kvP r w m).2 f₁ =ᶠ[𝓝 c] (kvP r w m).2 f₂ := by
  intro m
  induction m with
  | zero =>
    intro f₁ f₂ c h
    exact ⟨h, EventuallyEq.rfl⟩
  | succ m ih =>
    intro f₁ f₂ c h
    have hin : (fun c' => (w - (m : ℂ)) • f₁ c' - pbN r (r - m - 1) f₁ c') =ᶠ[𝓝 c]
        (fun c' => (w - (m : ℂ)) • f₂ c' - pbN r (r - m - 1) f₂ c') := by
      filter_upwards [h, pbN_germ (r - m - 1) h] with c' h1 h2
      rw [h1, h2]
    have ih1 := ih _ _ c hin
    have ih2 := ih f₁ f₂ c h
    simp only [kvP]
    refine ⟨?_, ih2.1⟩
    show (fun c' => (kvP r w m).1 _ c' - cbN r (r - m) (cbiN r (r - m - 1) ((kvP r w m).2 f₁)) c') =ᶠ[𝓝 c]
      (fun c' => (kvP r w m).1 _ c' - cbN r (r - m) (cbiN r (r - m - 1) ((kvP r w m).2 f₂)) c')
    filter_upwards [ih1.1, cbN_germ (r - m) (cbiN_germ (r - m - 1) ih2.2)] with c' h1 h2
    rw [h1, h2]

theorem vABm_germ (y : ℂ) : ∀ (m : ℕ) (f₁ f₂ : (Fin r → ℂ) → X) (c : Fin r → ℂ), f₁ =ᶠ[𝓝 c] f₂ →
    (vABm r y m).1 f₁ =ᶠ[𝓝 c] (vABm r y m).1 f₂ ∧ (vABm r y m).2 f₁ =ᶠ[𝓝 c] (vABm r y m).2 f₂ := by
  intro m
  induction m with
  | zero =>
    intro f₁ f₂ c h
    exact ⟨h, EventuallyEq.rfl⟩
  | succ i ih =>
    intro f₁ f₂ c h
    have hgerm := ih f₁ f₂ c h
    by_cases hi : i < r
    · simp only [vABm, dite_eq_left hi]
      refine ⟨?_, cbiOp_germ _ hgerm.1⟩
      filter_upwards [hgerm.1, pbOp_germ ⟨i, hi⟩ hgerm.1, cbOp_germ ⟨i, hi⟩ hgerm.2] with c' h1 h2 h3
      simp only [Pi.sub_apply, Pi.smul_apply]
      rw [h1, h2, h3]
    · simp only [vABm, dite_eq_right hi]
      exact hgerm

end Formalism.FourierDecayAlt.P.CutMP.TVCrdGerm
