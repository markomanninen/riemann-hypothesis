module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralBoundOfParts

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem np_top_two (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (a a' : C.LPt)
    (ha : D.IsLocPt a P.r) (ha' : D.IsLocPt a' P.r) (w : List C.Letter) (c : ℂ) :
    ((√(C.nAux P.k P.r 0 (fun _ _ => 1) 1 a) * √(C.nAux P.k P.r 0 (fun _ _ => 1) 1 a') / TBB.normC nn w : ℝ) : ℂ) *
        ((KB.levW P (P.r + 1) c : ℂ) * p.RR F (P.r + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)])) =
      TBB.NP p nn F (P.r + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)]) := by
  set A := C.nAux P.k P.r 0 (fun _ _ => 1) 1 a with hAdef
  set A' := C.nAux P.k P.r 0 (fun _ _ => 1) 1 a' with hA'def
  have hA : 0 ≤ A := TBBx5.weighted_auxiliary_norm_nonneg P P.r le_rfl a ha
  have hA' : 0 ≤ A' := TBBx5.weighted_auxiliary_norm_nonneg P P.r le_rfl a' ha'
  have hn : ∀ (b : C.LPt), D.IsLocPt b P.r → TBB.nPt P.k P.r (TBB.TTp p) (b ++ [(1, c)]) =
      C.nAux P.k P.r 0 (fun _ _ => 1) 1 b *
        C.nAux P.k P.r (D.ptGG (TBB.TTp p) (b ++ [(1, c)])) (fun _ _ => 1) (1 + P.r) [(1, c)] := by
    intro b hb
    unfold TBB.nPt
    rw [Formalism.FourierDecayAlt.P.PBD.weight_product_append, hb.2,
      Formalism.FourierDecayAlt.P.PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 (fun _ _ => 1) b 1 le_rfl (by rw [hb.2]; omega)]
  unfold TBB.NP
  rw [hn a ha, hn a' ha']
  by_cases hc2 : Complex.normSq c ≤ Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z'
  · have h0 : p.RR F (P.r + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)]) = 0 :=
      Formalism.FourierDecayAlt.P.PBD.rrTop_zero P p.l0 p.T p.ν' p.m₀ p.Θ p.TP (M.sgn P p.l0) F w a (a' ++ [(1, c)]) c ha.2 hc2
    rw [h0]
    simp
  · push Not at hc2
    have hT : Tz P.k P.r p.T.base.z = P.T := p.hP.2.2.2.1
    have hT' : Tz P.k P.r p.T.base.z' = P.T' := p.hP.2.2.2.2.1
    have hlast : ∀ b : C.LPt, D.ptGG (TBB.TTp p) (b ++ [(1, c)]) = Complex.normSq c - TBB.TTp p := by
      intro b
      simp [D.ptGG, D.ptLast]
    have hTT : TBB.TTp p = P.T * P.T' := by
      unfold TBB.TTp
      rw [hT, hT']
    have hfac : ∀ b : C.LPt, C.nAux P.k P.r (D.ptGG (TBB.TTp p) (b ++ [(1, c)])) (fun _ _ => 1) (1 + P.r) [(1, c)] =
        KB.levW P (P.r + 1) c := by
      intro b
      rw [hlast, hTT]
      rw [hT, hT'] at hc2
      simp only [C.nAux, KB.levW, B2.zWeight, if_pos hc2.le]
      rw [if_pos ⟨by omega, trivial⟩]
      simp
    have hlev : 0 ≤ KB.levW P (P.r + 1) c := by
      rw [← hfac a, hlast]
      simp only [C.nAux]
      rw [if_pos ⟨by omega, trivial⟩]
      have : 0 ≤ Complex.normSq c - TBB.TTp p := by
        unfold TBB.TTp; linarith
      simpa using pow_nonneg this _
    rw [hfac a, hfac a', Real.sqrt_mul hA, Real.sqrt_mul hA']
    have hs : √(KB.levW P (P.r + 1) c) * √(KB.levW P (P.r + 1) c) = KB.levW P (P.r + 1) c :=
      Real.mul_self_sqrt hlev
    have : √A * √(KB.levW P (P.r + 1) c) * (√A' * √(KB.levW P (P.r + 1) c)) / TBB.normC nn w =
        √A * √A' / TBB.normC nn w * KB.levW P (P.r + 1) c := by
      have e : √A * √(KB.levW P (P.r + 1) c) * (√A' * √(KB.levW P (P.r + 1) c)) / TBB.normC nn w =
          √A * √A' / TBB.normC nn w * (√(KB.levW P (P.r + 1) c) * √(KB.levW P (P.r + 1) c)) := by ring
      rw [e, hs]
    rw [this]
    push_cast
    ring

end place

end

end Formalism.FourierDecayAlt.P.CutBP.GT
