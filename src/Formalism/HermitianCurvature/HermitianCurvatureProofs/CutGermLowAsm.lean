module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLow
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermPartsCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinLeTruncatedExponential

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

theorem gl_isLocPt_snoc {a : C.LPt} {j m : ℕ} (ha : D.IsLocPt a j) (hm : 1 ≤ m) {c : ℂ} (hc : c ≠ 0) :
    D.IsLocPt (a ++ [(m, c)]) (j + m) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases List.mem_append.1 hx with hx | hx
    · exact ha.1 x hx
    · simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨hm, hc⟩
  · rw [← ha.2]
    simp [D.ptSize, List.map_append, List.sum_append]

theorem gl_fsv (σ z : ℂ) : P5.fsv σ z = G.psi (-U.betaU) (1 * σ * z) := by
  rw [TBBx1.fsv_eq]
  unfold G.psi U.betaU Formalism.QuantumDeterminants.cStd
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, Complex.one_im]
  push_cast
  ring

section vec

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem gl_inner_self (u : H) : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl

end vec

end

end Formalism.FourierDecayAlt.P.CutBP
