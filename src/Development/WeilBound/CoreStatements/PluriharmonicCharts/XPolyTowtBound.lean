module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace PositivityTheory.Xgp.poly_towt_bound

theorem abs_coeff_le {σ : Type} (P : MvPolynomial σ ℝ) (m : σ →₀ ℕ) :
    |P.coeff m| ≤ ∑ d ∈ P.support, |P.coeff d| := by
  by_cases h : m ∈ P.support
  · exact Finset.single_le_sum (f := fun d => |P.coeff d|) (fun _ _ => abs_nonneg _) h
  · rw [notMem_support_iff.mp h, abs_zero]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem gen {σ : Type} [Fintype σ] (f : σ → MvPolynomial σ ℝ) (hf : ∀ i, (f i).IsHomogeneous 1) (n : ℕ) :
    ∃ Cst : ℝ, 0 ≤ Cst ∧ ∀ (Q : MvPolynomial σ ℝ) (M : ℝ), Q.IsHomogeneous n →
      (aeval f Q).IsHomogeneous n ∧ ((∀ m, |Q.coeff m| ≤ M) →
        ∀ m, |(aeval f Q).coeff m| ≤ Cst * M) := by
  classical
  let S : Finset (σ →₀ ℕ) := (Finsupp.finite_of_degree_le (σ := σ) n).toFinset
  let image (d : σ →₀ ℕ) := aeval f (monomial d (1 : ℝ))
  let B (d : σ →₀ ℕ) : ℝ := ∑ e ∈ (image d).support, |(image d).coeff e|
  have hB : ∀ d, 0 ≤ B d := fun d => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨∑ d ∈ S, B d, Finset.sum_nonneg fun d _ => hB d, fun Q M hQ => ⟨?_, fun hM m => ?_⟩⟩
  · simpa only [one_mul] using hQ.aeval f hf
  · have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    have hsub : Q.support ⊆ S := by
      intro d hd
      simp only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      by_contra hne
      exact (mem_support_iff.mp hd) (hQ.coeff_eq_zero (by omega))
    have e : (aeval f Q).coeff m = ∑ d ∈ Q.support, Q.coeff d * (image d).coeff m := by
      conv_lhs => rw [Q.as_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, coeff_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      have hmonomial : monomial d (Q.coeff d) = C (Q.coeff d) * monomial d (1 : ℝ) := by
        rw [C_mul_monomial, mul_one]
      rw [hmonomial, map_mul, aeval_C, algebraMap_eq, coeff_C_mul]
    rw [e]
    calc _ ≤ ∑ d ∈ Q.support, |Q.coeff d * (image d).coeff m| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Q.support, B d * M := by
          refine Finset.sum_le_sum fun d _ => ?_
          rw [abs_mul, mul_comm]
          exact mul_le_mul (abs_coeff_le _ m) (hM d) (abs_nonneg _) (hB d)
      _ ≤ ∑ d ∈ S, B d * M :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => mul_nonneg (hB d) hM0
      _ = _ := by rw [Finset.sum_mul]

theorem gapX_hom {Ψ : Type} {N : ℕ} (p : Ψ × Fin N) : (gapX p).IsHomogeneous 1 := by
  unfold gapX
  refine (isHomogeneous_X ℝ p).sub ?_
  split_ifs
  · exact isHomogeneous_X ℝ _
  · exact isHomogeneous_zero _ _ _

end PositivityTheory.Xgp.poly_towt_bound

theorem PositivityTheory.Xgp.t_poly_towt_bound :
    ∀ (Ψ : Type) [Fintype Ψ] (N n : ℕ), ∃ Cst : ℝ,
      (∀ (Q : MvPolynomial (Ψ × Fin N) ℝ) (M : ℝ), Q.IsHomogeneous n →
        (toWt Q).IsHomogeneous n ∧ ((∀ m, |Q.coeff m| ≤ M) →
          ∀ m, |(toWt Q).coeff m| ≤ Cst * M)) ∧
      ∀ (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (M : ℝ), Q.IsHomogeneous n →
        (toWtS Q).IsHomogeneous n ∧ ((∀ m, |Q.coeff m| ≤ M) →
          ∀ m, |(toWtS Q).coeff m| ≤ Cst * M) := by
  intro Ψ _ N n
  obtain ⟨C1, h1, H1⟩ := PositivityTheory.Xgp.poly_towt_bound.gen (gapX (Ψ := Ψ) (N := N))
    PositivityTheory.Xgp.poly_towt_bound.gapX_hom n
  obtain ⟨C2, h2, H2⟩ := PositivityTheory.Xgp.poly_towt_bound.gen
    (fun o : Option (Ψ × Fin N) => o.elim (X none) fun p => rename some (gapX p)) (by
      rintro (_ | p)
      · exact isHomogeneous_X ℝ _
      · exact (PositivityTheory.Xgp.poly_towt_bound.gapX_hom p).rename_isHomogeneous) n
  refine ⟨C1 + C2, fun Q M hQ => ⟨(H1 Q M hQ).1, fun hM m => ?_⟩,
    fun Q M hQ => ⟨(H2 Q M hQ).1, fun hM m => ?_⟩⟩
  · have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    have := (H1 Q M hQ).2 hM m
    have h3 := mul_nonneg h2 hM0
    unfold toWt
    linarith
  · have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    have := (H2 Q M hQ).2 hM m
    have h3 := mul_nonneg h1 hM0
    unfold toWtS
    linarith
