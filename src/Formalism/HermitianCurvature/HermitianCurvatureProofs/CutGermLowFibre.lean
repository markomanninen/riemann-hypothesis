module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLow
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralBoundOfParts

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt MeasureTheory
open scoped ComplexConjugate

noncomputable section

open Classical

theorem nPt_append_one (P : M.Par) (TT : ℝ) (a : C.LPt) (j : ℕ) (ha : D.IsLocPt a j) (hj : j + 1 ≤ P.r) (c : ℂ) :
    TBB.nPt P.k P.r TT (a ++ [(1, c)]) = TBB.nPt P.k P.r TT a * KB.levW P (j + 1) c := by
  let GG := D.ptGG TT (a ++ [(1, c)])
  let GG' := D.ptGG TT a
  have happend : ∀ (l : C.LPt) (b : ℕ), b + D.ptSize l = j + 1 →
      C.nAux P.k P.r GG (fun _ _ => 1) b (l ++ [(1, c)]) =
        C.nAux P.k P.r GG' (fun _ _ => 1) b l * KB.levW P (j + 1) c := by
    intro l
    induction l with
    | nil =>
      intro b hb
      change b + 0 = j + 1 at hb
      rw [Nat.add_zero] at hb
      subst b
      have htop : j + 1 ≠ P.r + 1 := by omega
      have hexp : C.Mlev P.k P.r (j + 1) + 1 - 3 = C.Mlev P.k P.r (j + 1) - 2 := by ring
      simp only [List.nil_append, C.nAux, KB.levW, Nat.add_sub_cancel, htop, false_and,
        if_false, Nat.cast_one, one_mul, mul_one, hexp]
    | cons x l ih =>
      rcases x with ⟨s, t⟩
      intro b hb
      change b + (s + D.ptSize l) = j + 1 at hb
      have htop : b + s - 1 ≠ P.r + 1 := by omega
      simp only [List.cons_append, C.nAux, htop, false_and, if_false, ih (b + s) (by omega), mul_assoc]
  exact happend a 1 (by rw [ha.2, Nat.add_comm])

theorem nPt_nonneg_loc (P : M.Par) (TT : ℝ) (a : C.LPt) (j : ℕ) (ha : D.IsLocPt a j) (hj : j ≤ P.r) :
    0 ≤ TBB.nPt P.k P.r TT a := by
  have hnonneg : ∀ (l : C.LPt) (b : ℕ), b + D.ptSize l ≤ P.r + 1 →
      0 ≤ C.nAux P.k P.r (D.ptGG TT a) (fun _ _ => 1) b l := by
    intro l
    induction l with
    | nil =>
      intro b _
      simp [C.nAux]
    | cons x l ih =>
      rcases x with ⟨s, t⟩
      intro b hb
      change b + (s + D.ptSize l) ≤ P.r + 1 at hb
      have htop : b + s - 1 ≠ P.r + 1 := by omega
      simp only [C.nAux, htop, false_and, if_false, one_mul]
      exact mul_nonneg (zpow_nonneg (norm_nonneg _) _) (ih (b + s) (by omega))
  exact hnonneg a 1 (by rw [ha.2]; omega)

theorem levW_nonneg_low (P : M.Par) (j : ℕ) (hj : j + 1 ≤ P.r) (c : ℂ) : 0 ≤ KB.levW P (j + 1) c := by
  simp only [KB.levW]
  rw [if_neg (by omega)]
  exact zpow_nonneg (norm_nonneg _) _

theorem glFibre : GLFibre := by
  intro hA Wp Wq _ _ _ _ _ _ P p nn F Y N Cb hCb hF hnn j hj w hw hN a b ha hb
  have hPS : KB.PStd := Formalism.FourierDecayAlt.P.standard_pairing_of_heads Formalism.FourierDecayAlt.P.radial_head Formalism.FourierDecayAlt.P.head_top
  have hjr : j ≤ P.r := by omega
  obtain ⟨φ, -, hφi, hφ, hφs⟩ := hPS hA Wp Wq P p F j hjr w a b ha hb Cb hCb hF hw.1
  set K : ℝ := Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) b) /
    TBB.normC nn w with hK
  have hae : (fun c => TBB.NP p nn F (j + 1) w (a ++ [(1, c)]) (b ++ [(1, c)])) =ᵐ[volume]
      fun c => (K : ℂ) * φ c := by
    filter_upwards [Formalism.FourierDecayAlt.P.TBBx1.ae_ne_zero] with c hc
    rw [hφ c hc]
    unfold TBB.NP
    rw [nPt_append_one P _ a j ha hj c, nPt_append_one P _ b j hb hj c,
      Real.sqrt_mul (nPt_nonneg_loc P _ a j ha hjr), Real.sqrt_mul (nPt_nonneg_loc P _ b j hb hjr)]
    have hl := Real.mul_self_sqrt (levW_nonneg_low P j hj c)
    rw [hK]
    have : Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (KB.levW P (j + 1) c) *
        (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) b) * Real.sqrt (KB.levW P (j + 1) c)) / TBB.normC nn w =
        Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) b) / TBB.normC nn w *
          KB.levW P (j + 1) c := by
      calc _ = Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) b) /
              TBB.normC nn w * (Real.sqrt (KB.levW P (j + 1) c) * Real.sqrt (KB.levW P (j + 1) c)) := by ring
        _ = _ := by rw [hl]
    rw [this]
    push_cast
    ring
  refine ⟨(hφi.const_mul (K : ℂ)).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_const_mul]
  have h0 := hφs 0
  simp only [P5.fsv, zero_mul, map_zero, sub_zero, Complex.exp_zero, one_mul,
    Formalism.FourierDecayAlt.P.PBASM.waveG_zero_eq_self] at h0
  rw [h0]
  unfold TBB.NP
  congr 1
  unfold KB.Pl.RR D.RRplace
  rw [dite_eq_left ⟨ha, hb⟩, dite_eq_left hjr]
  rfl

end

end Formalism.FourierDecayAlt.P.CutBP
