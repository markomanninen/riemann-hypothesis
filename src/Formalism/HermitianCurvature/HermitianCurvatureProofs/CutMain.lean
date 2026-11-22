module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LimZeroNPf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem amaps_id (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) :
    Amaps p f (fun _ => ContinuousLinearMap.id ℂ Wq) (fun _ => ContinuousLinearMap.id ℂ Wq)
      (fun _ => ContinuousLinearMap.id ℂ Wq) (fun _ => ContinuousLinearMap.id ℂ Wq) b 0 := by
  refine ⟨fun γ _ _ => by simp, fun γ _ _ => by simp, fun γ _ _ v => ?_, fun γ _ _ => ?_, fun γ _ _ => ?_⟩
  · simp only [mul_zero, pow_zero, one_mul, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply]
    nlinarith [sq_nonneg ‖v‖]
  · rw [pow_zero]
    exact pow_le_one₀ (norm_nonneg _) ContinuousLinearMap.norm_id_le
  · rw [pow_zero]
    exact pow_le_one₀ (norm_nonneg _) ContinuousLinearMap.norm_id_le

end place


end

end Formalism.FourierDecayAlt.P.CutBP
