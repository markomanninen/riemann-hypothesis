module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HilbertSchmidtLowerBoundInverseDifferent
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.Complexify

@[expose] public section

open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSchmidt_lower_bound_inverseDifferent :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (a b : ℕ)
      (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
      (X' : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ)
      (A : Submodule (𝓞 K) (Fin a → K)) (B : Submodule (𝓞 K) (Fin b → K)) (lo hi : ℝ),
      (∀ w, IsUnit (X w).det) → (∀ w, IsUnit (X' w).det) → A.FG → B.FG → 0 < lo →
      (∀ N, N ≤ A → N ≠ ⊥ → lo ≤ Formalism.HN.size (Pi.basisFun K (Fin a)) X N) →
      Formalism.HN.largestSize (Pi.basisFun K (Fin b)) X' B ≤ hi →
      ∀ ψ : Matrix (Fin a) (Fin b) K, (∃ y ∈ B, ψ *ᵥ y ≠ 0) →
        (∀ δ ∈ differentIdeal ℤ (𝓞 K), ∀ y ∈ B, δ • (ψ *ᵥ y) ∈ A) →
        (Formalism.HN.nPl K : ℝ) *
            (lo / (|(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ))) * hi)) ^ 2 ≤
          ∑ w, ∑ i, ∑ j, ‖((X w)⁻¹ * ψ.map w.embedding * X' w) i j‖ ^ 2 := by
  intro K _ _ _ _ a b X X' A B lo hi hX hX' _ hB hlo hA hhi ψ ⟨y, hyB, hy⟩ hψ
  let φ : (Fin b → K) →ₗ[K] (Fin a → K) := Matrix.toLin' ψ
  let A' : Submodule (𝓞 K) (Fin a → K) := B.map (φ.restrictScalars (𝓞 K))
  let rd : ℝ := |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ)))
  have hrdpos : 0 < rd :=
    Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero K)) _
  have hA'fg : A'.FG := hB.map _
  have hA'0 : A' ≠ ⊥ := by
    intro h
    have hmem : ψ *ᵥ y ∈ A' := ⟨y, hyB, by simp [φ]⟩
    rw [h] at hmem
    exact hy hmem
  have hB0 : B ≠ ⊥ := by
    intro h
    apply hA'0
    simp [A', h]
  have hd : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  have hleast : lo / rd ≤ leastSize (Pi.basisFun K (Fin a)) X A' := by
    refine le_csInf ⟨_, A', le_rfl, hA'0, rfl⟩ ?_
    rintro t ⟨N, hN, hN0, rfl⟩
    have hNfg : N.FG := Submodule.FG.of_le hA'fg hN
    have hle : differentIdeal ℤ (𝓞 K) • N ≤ A := by
      refine Submodule.smul_le.2 fun δ hδ v hv => ?_
      obtain ⟨z, hz, rfl⟩ := hN hv
      simpa [φ] using hψ δ hδ z hz
    have hspan := Formalism.HN.DualPolygon.twist_span_smul N _ hd
    have hne : differentIdeal ℤ (𝓞 K) • N ≠ ⊥ := by
      intro h
      rw [h] at hspan
      apply hN0
      rw [eq_bot_iff]
      intro v hv
      have hmem : v ∈ Submodule.span K (N : Set (Fin a → K)) := Submodule.subset_span hv
      rw [← hspan] at hmem
      simpa using hmem
    have hsize :
        Formalism.HN.size (Pi.basisFun K (Fin a)) X (differentIdeal ℤ (𝓞 K) • N) =
          Formalism.HN.size (Pi.basisFun K (Fin a)) X N * rd := by
      have hrk : rkK (differentIdeal ℤ (𝓞 K) • N) = rkK N := by
        unfold rkK
        rw [hspan]
      have hnorm : (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) =
          |(NumberField.discr K : ℝ)| := by
        rw [NumberField.absNorm_differentIdeal K (𝓞 K), Nat.cast_natAbs, Int.cast_abs]
      have hj : (rkK N : ℝ) ≠ 0 := by
        exact_mod_cast (Formalism.LFunctionChainParameters.slopeLatticeData.rkK_pos hN0).ne'
      have hf : (Formalism.HN.nPl K : ℝ) ≠ 0 := by
        have hcard : 0 < Formalism.HN.nPl K := Fintype.card_pos
        exact_mod_cast hcard.ne'
      unfold Formalism.HN.size rd
      rw [Formalism.LFunctionChainParameters.slopeLatticeData.ht_ideal _ X hX hNfg hd, hrk, hnorm,
        Real.mul_rpow (Formalism.LFunctionChainParameters.slopeLatticeData.ht_pos _ X hX hNfg).le
          (by positivity),
        ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      congr 2
      field_simp
    rw [div_le_iff₀ hrdpos, ← hsize]
    exact hA _ hle hne
  have hLpos : 0 < Formalism.HN.largestSize (Pi.basisFun K (Fin b)) X' B := by
    rw [(sizeMu K _ _ (Pi.basisFun K (Fin b)) X' hX' B hB hB0).2.2.2.2.1]
    exact Real.exp_pos _
  have hM := sizeIneq K _ _ _ _ (Pi.basisFun K (Fin b)) X' (Pi.basisFun K (Fin a)) X hX' hX φ B A'
    hB hA'fg le_rfl hA'0
  have h4 : lo / (rd * hi) ≤
      (∏ v, opNormAt (Pi.basisFun K (Fin b)) X' (Pi.basisFun K (Fin a)) X v φ) ^
        ((1 : ℝ) / (Formalism.HN.nPl K : ℝ)) := by
    refine le_trans ?_ hM
    rw [← div_div]
    exact div_le_div₀ ((div_pos hlo hrdpos).le.trans hleast) hleast hLpos hhi
  have h5 := GlobalTheory.DualBound.card_mul_geom_sq_le
    (fun v => opNormAt (Pi.basisFun K (Fin b)) X' (Pi.basisFun K (Fin a)) X v φ)
    (fun v => norm_nonneg _)
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (div_nonneg hlo.le (mul_nonneg hrdpos.le (hLpos.le.trans hhi))) h4 2)
      (Nat.cast_nonneg _)
    _ ≤ _ := h5
    _ ≤ _ := by
      refine Finset.sum_le_sum fun w _ => ?_
      have hmatrix : LinearMap.toMatrix (Pi.basisFun K (Fin b)) (Pi.basisFun K (Fin a)) φ = ψ := by
        ext i j
        simp [φ]
      unfold opNormAt
      rw [hmatrix]
      exact GlobalTheory.DualBound.opNorm_sq_le_hs _
