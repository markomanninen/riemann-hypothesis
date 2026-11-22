module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMain
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimE

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology

noncomputable section

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def LimEvT (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) : Prop :=
  ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
    Tendsto (fun ε : ℝ => (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re) (𝓝[>] 0) (𝓝 (p.RR F 0 w [] []).re)

theorem limE_of_partsT (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (N : ℕ) (hnn : ∀ y, 0 ≤ nn y) (hEv : LimEvT p χ F Y N) (hPos : LimPos p F Y N)
    (hBd : LimBd p nn F Y N) : LimE p nn χ F Y N := by
  intro w hw hl
  have hE := hEv w hw hl
  have hP := hPos w hw hl
  have hB := hBd w hw hl
  have hN : 0 ≤ TBB.normC nn w := by
    unfold TBB.normC
    exact List.prod_nonneg (fun x hx => by
      obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx
      exact hnn _)
  by_cases hb : 0 < (B.beta p.T.base F F).re
  · refine ⟨(p.RR F 0 w [] []).re / (B.beta p.T.base F F).re, div_nonneg hP hb.le, (div_le_iff₀ hb).2 hB, ?_⟩
    rw [div_mul_cancel₀ _ hb.ne']
    exact hE
  · have hb' : (B.beta p.T.base F F).re ≤ 0 := not_lt.1 hb
    have hR0 : (p.RR F 0 w [] []).re = 0 :=
      le_antisymm (hB.trans (mul_nonpos_of_nonneg_of_nonpos hN hb')) hP
    refine ⟨0, le_refl 0, hN, ?_⟩
    rw [zero_mul]
    rw [hR0] at hE
    exact hE

end place


end

end Formalism.FourierDecayAlt.P.CutBP
