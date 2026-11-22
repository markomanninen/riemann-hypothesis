module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreLocal
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StDiagFibreFubini

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace DiagFibreMoment

theorem coeff_momentPoly {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ)
    (Q : MvPolynomial (Fin 3) (Ω → ℝ)) (m : Fin 3 →₀ ℕ) :
    AddMonoidAlgebra.coeff (momentPoly μ w Q) m = ∫ p, w p * AddMonoidAlgebra.coeff Q m p ∂μ := by
  rw [momentPoly, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h]
    simp

theorem momentPoly_sum {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ) (s : Finset ι)
    (Q : ι → MvPolynomial (Fin 3) (Ω → ℝ)) (hQ : ∀ i ∈ s, ∀ m, Integrable (fun p => w p * AddMonoidAlgebra.coeff (Q i) m p) μ) :
    momentPoly μ w (∑ i ∈ s, Q i) = ∑ i ∈ s, momentPoly μ w (Q i) := by
  ext m
  rw [coeff_momentPoly, coeff_sum, coeff_sum]
  simp only [coeff_momentPoly, Finset.sum_apply, Finset.mul_sum]
  exact integral_finsetSum s fun i hi => hQ i hi m

theorem continuous_coeff_aeval (Q : MvPolynomial (Fin 2) ℝ) (m : Fin 3 →₀ ℕ) :
    Continuous (AddMonoidAlgebra.coeff (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] Q) m) := by
  set φ : C(S2 × S2, ℝ) →ₐ[ℝ] (S2 × S2 → ℝ) := ContinuousMap.coeFnAlgHom (α := S2 × S2) (A := ℝ) ℝ
  set v : Fin 2 → MvPolynomial (Fin 3) C(S2 × S2, ℝ) :=
    ![∑ i, X i * C ((FibreLocal.coordS i).comp ContinuousMap.fst),
      ∑ i, X i * C ((FibreLocal.coordS i).comp ContinuousMap.snd)]
  have hv : ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] = fun r => mapAlgHom φ (v r) := by
    funext r
    fin_cases r
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [Fin.zero_eta, Matrix.cons_val_zero, v, dotPoly, mapAlgHom_apply, map_sum, map_mul, map_X, map_C]
        apply Finset.sum_congr rfl
        intro i hi
        congr 2
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, v, dotPoly, mapAlgHom_apply, map_sum,
        map_mul, map_X, map_C]
        apply Finset.sum_congr rfl
        intro i hi
        congr 2
  rw [hv, ← comp_aeval, AlgHom.comp_apply, mapAlgHom_apply, coeff_map]
  exact (AddMonoidAlgebra.coeff (aeval v Q) m).continuous

theorem sum_words (k : ℕ) :
    ∑ i ∈ Finset.range k, ((X 0 - X 1) * X 0 ^ (2 * i) * X 1 ^ (2 * k - 1 - 2 * i) : MvPolynomial (Fin 2) ℝ) =
      gPoly k := by
  rw [FibreLocal.gPoly_eq, FlagBundles.gKernel]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik := Finset.mem_range.1 hi
  rw [show 2 * k - 2 * i = (2 * k - 1 - 2 * i) + 1 by omega, pow_succ, pow_succ]
  ring

theorem sum_diagWordMomentPoly (k : ℕ) :
    ∑ i ∈ Finset.range k, diagWordMomentPoly k i = fibreMomentPoly k := by
  simp only [diagWordMomentPoly]
  rw [← momentPoly_sum _ _ _ _ fun i _ m =>
    FibreLocal.integrable_mul _ (continuous_coeff_aeval _ m)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, ← map_sum, ← map_sum, sum_words]
  rfl

end DiagFibreMoment

end

end GroundTheory.Heights₂.Heights.Inter
