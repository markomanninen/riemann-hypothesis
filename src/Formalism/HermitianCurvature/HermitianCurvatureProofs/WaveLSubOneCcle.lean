module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormExpMulISubOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormLetterScal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveDiffForm

@[expose] public section

noncomputable section

namespace Formalism.FourierDecayAlt.P.StandardPairingDecay

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section one

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem waveL_sub_one_ccle (Bs : B.RealPlaceData k ρ Wp Wq) (w : List C.Letter) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℂ, ‖σ‖ ≤ 2 → ∀ (A : ℝ) (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (c : ℝ),
      (∀ e, B.CCle (A + ((m + 1 : ℕ) : ℝ)) m (x e) c) →
      ∀ e, B.CCle A m (((PBO.waveL Bs σ w - 1) x) e) (K * ‖σ‖ * c) := by
  have uInv_ccle (A : ℝ) (m : ℕ) (σ : ℂ) (hσ : ‖σ‖ ≤ 2) :
      ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (c : ℝ),
        (∀ e, B.CCle A m (x e) c) → ∀ e,
        B.CCle A m (KB.uInv σ w x e) (3 ^ w.length * c) ∧
        B.CCle A m (fun g => KB.uInv σ w x e g - x e g) (3 ^ w.length * ‖σ‖ * c) := by
    intro w
    induction w with
    | nil =>
      intro x c hx e
      have hc : 0 ≤ c := JCx2.pd_ccle_nonneg (hx e)
      refine ⟨by simpa [KB.uInv] using hx e, ?_⟩
      simp only [KB.uInv, sub_self, List.length_nil, pow_zero, one_mul]
      exact JCx2.pd_ccle_mono_c BetaSesquilinearity.CCle_zero (by positivity)
    | cons l w ih =>
      intro x c hx e
      have hc : 0 ≤ c := JCx2.pd_ccle_nonneg (hx e)
      have ih0 := ih (fun e' => x (Fin.cons (0 : Fin 2) e')) c (fun e' => hx _) (fun a => e a.succ)
      have ih1 := ih (fun e' => x (Fin.cons (1 : Fin 2) e')) c (fun e' => hx _) (fun a => e a.succ)
      have hs : ‖(if l.1 then σ else (starRingEnd ℂ) σ)‖ = ‖σ‖ := (by cases l.1 <;> simp)
      have h3 : (0 : ℝ) ≤ 3 ^ w.length := by positivity
      have hσ0 : 0 ≤ ‖σ‖ := norm_nonneg _
      have hlen : (l :: w).length = w.length + 1 := rfl
      have hce : e = Fin.cons (e 0) (fun a => e a.succ) := (Fin.cons_self_tail e).symm
      have hp : (3 : ℝ) ^ (l :: w).length = 3 * 3 ^ w.length := by rw [hlen, pow_succ, mul_comm]
      simp only [KB.uInv]
      by_cases he : e 0 = 0
      · rw [if_pos he]
        have hxe : x e = x (Fin.cons (0 : Fin 2) (fun a => e a.succ)) := by
          conv_lhs => rw [hce, he]
        refine ⟨JCx2.pd_ccle_mono_c ih0.1 (by rw [hp]; nlinarith), ?_⟩
        rw [hxe]
        exact JCx2.pd_ccle_mono_c ih0.2 (by rw [hp]; nlinarith [mul_nonneg h3 hσ0])
      · rw [if_neg he]
        have he1 : e 0 = 1 := by
          rcases Fin.exists_fin_two.1 ⟨e 0, rfl⟩ with h | h
          · exact absurd h he
          · exact h
        have hxe : x e = x (Fin.cons (1 : Fin 2) (fun a => e a.succ)) := by
          conv_lhs => rw [hce, he1]
        refine ⟨?_, ?_⟩
        · have := BetaSesquilinearity.CCle_add ih1.1 (BetaSesquilinearity.CCle_smul (if l.1 then σ else (starRingEnd ℂ) σ) ih0.1)
          rw [hs] at this
          exact JCx2.pd_ccle_mono_c (show B.CCle A m ((KB.uInv σ w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ)) +
            (if l.1 then σ else (starRingEnd ℂ) σ) • KB.uInv σ w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ)) _ from this)
            (by rw [hp]; nlinarith [mul_nonneg h3 hc])
        · have := BetaSesquilinearity.CCle_add ih1.2 (BetaSesquilinearity.CCle_smul (if l.1 then σ else (starRingEnd ℂ) σ) ih0.1)
          rw [hs] at this
          rw [hxe]
          have hf : (fun g => (KB.uInv σ w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ) +
              (if l.1 then σ else (starRingEnd ℂ) σ) • KB.uInv σ w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ)) g -
              x (Fin.cons (1 : Fin 2) (fun a => e a.succ)) g) =
              fun g => (KB.uInv σ w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ) g -
                x (Fin.cons (1 : Fin 2) (fun a => e a.succ)) g) +
                (if l.1 then σ else (starRingEnd ℂ) σ) • KB.uInv σ w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ) g := by
            funext g
            simp only [Pi.add_apply, Pi.smul_apply]
            abel
          rw [hf]
          exact JCx2.pd_ccle_mono_c this (by rw [hp]; nlinarith [mul_nonneg h3 hc, mul_nonneg (mul_nonneg h3 hσ0) hc])
  obtain ⟨K1, hK1, hmul⟩ := mult_phase (E := Wq →L[ℂ] Wp) m
    (JCx2.mnLinHerm (fvec k ρ Bs.z' 0) (fvec k ρ Bs.z 0))
  refine ⟨(K1 + 1) * 3 ^ w.length, by positivity, ?_⟩
  intro σ hσ A x c hx e
  have hc : 0 ≤ c := JCx2.pd_ccle_nonneg (hx e)
  have hu := uInv_ccle (A + ((m + 1 : ℕ) : ℝ)) m σ hσ w x c hx e
  have h1 := hmul σ hσ A (KB.uInv σ w x e) (3 ^ w.length * c) hu.1
  have h2 : B.CCle A m (fun g => KB.uInv σ w x e g - x e g) (3 ^ w.length * ‖σ‖ * c) :=
    BetaSesquilinearity.CCle_mono_A (by have : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _; linarith) hu.2
  have h3 := BetaSesquilinearity.CCle_add h1 h2
  have hf : ((PBO.waveL Bs σ w - 1) x) e = fun g =>
      (Complex.exp (PBFV.phaseL σ (JCx2.mnLinHerm (fvec k ρ Bs.z' 0) (fvec k ρ Bs.z 0)) g) - 1) •
        KB.uInv σ w x e g + (KB.uInv σ w x e g - x e g) := by
    funext g
    simp only [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, PBO.waveL, LinearMap.coe_mk,
      AddHom.coe_mk, KB.waveG]
    rw [PBFV.fsv_dmin_one σ Bs.z Bs.z' g (by omega), sub_smul, one_smul]
    abel
  rw [hf]
  refine JCx2.pd_ccle_mono_c h3 (le_of_eq ?_)
  ring

theorem mDiff_ccle (Bs : B.RealPlaceData k ρ Wp Wq) (w : List C.Letter) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℂ, ‖σ‖ ≤ 2 → ∀ (A : ℝ) (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (c : ℝ),
      (∀ e, B.CCle (A + 3 * ((m + 1 : ℕ) : ℝ)) m (x e) c) →
      ∀ e, B.CCle A m ((PBO.mDiff Bs σ w x) e) (K * ‖σ‖ ^ 3 * c) := by
  obtain ⟨K, hK, h1⟩ := waveL_sub_one_ccle Bs w m
  refine ⟨K ^ 3, by positivity, ?_⟩
  intro σ hσ A x c hx
  set M : ℝ := ((m + 1 : ℕ) : ℝ) with hM
  have hx' : ∀ e, B.CCle ((A + M + M) + M) m (x e) c := fun e => by
    have : (A + M + M) + M = A + 3 * M := by ring
    rw [this]; exact hx e
  have s1 := h1 σ hσ (A + M + M) x c hx'
  have s2 := h1 σ hσ (A + M) _ _ s1
  have s3 := h1 σ hσ A _ _ s2
  intro e
  have he : PBO.mDiff Bs σ w x = (PBO.waveL Bs σ w - 1) ((PBO.waveL Bs σ w - 1) ((PBO.waveL Bs σ w - 1) x)) := by
    simp only [PBO.mDiff, pow_succ, pow_zero, one_mul]
    rfl
  rw [he]
  refine JCx2.pd_ccle_mono_c (s3 e) (le_of_eq ?_)
  ring

end one

end Formalism.FourierDecayAlt.P.StandardPairingDecay
