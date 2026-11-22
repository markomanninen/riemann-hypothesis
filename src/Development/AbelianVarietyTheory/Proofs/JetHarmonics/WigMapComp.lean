module

public import Mathlib
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
public import Development.AbelianVarietyTheory.Definitions.Jets.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap

@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem wigMap_comp : ∀ (V₁ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] (V₃ : Type) [NormedAddCommGroup V₃] [InnerProductSpace ℂ V₃] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π₁ : Mx k r → (V₁ →L[ℂ] V₁)) (π₂ : Mx k r → (V₂ →L[ℂ] V₂)) (π₃ : Mx k r → (V₃ →L[ℂ] V₃)) (d e : ℕ) (A : (Fin (2 * r + k + 1) → ℂ) → (V₂ →L[ℂ] V₁)) (A' : (Fin (2 * r + k + 1) → ℂ) → (V₃ →L[ℂ] V₂)), GlobalTheory.WigSh.WigMap k r z π₂ π₁ d A → GlobalTheory.WigSh.WigMap k r z π₃ π₂ e A' → GlobalTheory.WigSh.WigMap k r z π₃ π₁ (d + e) (fun ω => (A ω).comp (A' ω)) := by
  intro V₁ _ _ V₂ _ _ V₃ _ _ k r z π₁ π₂ π₃ d e A A' hA hA'
  obtain ⟨⟨t, q, L, hq, hL⟩, h2, h3, h4⟩ := hA
  obtain ⟨⟨t', q', L', hq', hL'⟩, h2', h3', h4'⟩ := hA'
  refine ⟨⟨t * t', fun i => q (finProdFinEquiv.symm i).1 * q' (finProdFinEquiv.symm i).2,
    fun i => (L (finProdFinEquiv.symm i).1).comp (L' (finProdFinEquiv.symm i).2), ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i
    exact (MvPolynomial.totalDegree_mul _ _).trans (add_le_add (hq _) (hq' _))
  · intro ω
    rw [Equiv.sum_comp finProdFinEquiv.symm (fun p : Fin t × Fin t' =>
      MvPolynomial.eval (Sum.elim ω (fun j => star (ω j))) (q p.1 * q' p.2) • (L p.1).comp (L' p.2)),
      Fintype.sum_prod_type]
    show (A ω).comp (A' ω) = _
    rw [hL ω, hL' ω]
    ext x
    simp only [ContinuousLinearMap.comp_apply, sum_apply, ContinuousLinearMap.smul_apply,
      map_sum, map_smul, Finset.smul_sum, map_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_comm, smul_smul]
  · intro h hh ω
    show ((A (h *ᵥ ω)).comp (A' (h *ᵥ ω))).comp (π₃ h) = (π₁ h).comp ((A ω).comp (A' ω))
    rw [ContinuousLinearMap.comp_assoc, h2' h hh, ← ContinuousLinearMap.comp_assoc, h2 h hh,
      ContinuousLinearMap.comp_assoc]
  · intro s ω
    show (A ((s : ℂ) • ω)).comp (A' ((s : ℂ) • ω)) = ((s : ℂ) ^ (d + e)) • (A ω).comp (A' ω)
    rw [h3, h3', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul, pow_add]
  · intro ω hω hz
    show ‖(A ω).comp (A' ω)‖ ^ 2 ≤ _
    have a := h4 ω hω hz
    have b := h4' ω hω hz
    calc ‖(A ω).comp (A' ω)‖ ^ 2 ≤ (‖A ω‖ * ‖A' ω‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.opNorm_comp_le _ _) 2
      _ = ‖A ω‖ ^ 2 * ‖A' ω‖ ^ 2 := mul_pow _ _ _
      _ ≤ _ := by
          rw [pow_add]
          exact mul_le_mul a b (sq_nonneg _) ((sq_nonneg _).trans a)

end GlobalTheory.WigSh
