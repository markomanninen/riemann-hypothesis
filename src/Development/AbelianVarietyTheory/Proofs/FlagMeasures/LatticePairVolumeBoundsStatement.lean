module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticePairVolumeBounds
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.Complexify

@[expose] public section

open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset
open GlobalTheory.HomCover in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_pair_volume_bounds :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (a b : ℕ)
      (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
      (X' : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ)
      (A : Submodule (𝓞 K) (Fin a → K)) (B : Submodule (𝓞 K) (Fin b → K)) (lo hi : ℝ),
      (∀ w, IsUnit (X w).det) → (∀ w, IsUnit (X' w).det) → A.FG → B.FG →
      Submodule.span K (A : Set (Fin a → K)) = ⊤ →
      Submodule.span K (B : Set (Fin b → K)) = ⊤ → 0 < lo → 0 < hi →
      (∀ N, N ≤ A → N ≠ ⊥ → lo ≤ Formalism.HN.size (Pi.basisFun K (Fin a)) X N) →
      Formalism.HN.largestSize (Pi.basisFun K (Fin b)) X' B ≤ hi →
      ∀ T : InfinitePlace K → Matrix (Fin b) (Fin a) ℂ,
        ∃ φ : Matrix (Fin b) (Fin a) K, (∀ y ∈ A, φ *ᵥ y ∈ B) ∧
          Real.sqrt (∑ w, ∑ i, ∑ j, ‖(T w - (X' w)⁻¹ * φ.map w.embedding * X w) i j‖ ^ 2) ≤
            (a : ℝ) * b * Real.sqrt (Formalism.HN.nPl K) *
              |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ))) * hi / (2 * lo) := by
  intro K _ _ _ _ a b X X' A B lo hi hX hX' hA hB hAs hBs hlo hhi hlow hup T
  set rd : ℝ := |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ))) with hrd
  have hrd0 : 0 < rd := Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast discr_ne_zero K)) _
  have hn : (Fintype.card (InfinitePlace K) : ℝ) = (Formalism.HN.nPl K : ℝ) := rfl
  have hn0 : (0 : ℝ) < Formalism.HN.nPl K := by
    rw [← hn]; exact_mod_cast Fintype.card_pos
  have hs0 : 0 < Real.sqrt (Formalism.HN.nPl K) := Real.sqrt_pos.2 hn0
  have hss : Real.sqrt (Formalism.HN.nPl K) ^ 2 = Formalism.HN.nPl K := Real.sq_sqrt hn0.le
  obtain ⟨y, hy, hle⟩ := GlobalTheory.T.lattice_covering_of_trace_dual_lower_bound K (Fin b × Fin a) (Fin b × Fin a) (homLat A B)
    (fun w => frameEquiv (X' w) (X w) (hX' w) (hX w)) (Real.sqrt (Formalism.HN.nPl K) * (lo / (rd * hi)))
    (homLat_fg A B hA hB hAs) (homLat_span A B hA hBs) (by positivity)
    (fun f c hf hint hc => by
      have hc' : ∀ w, c w = fun p => ((X w)⁻¹ * ((toMat f)ᵀ).map w.embedding * X' w) p.2 p.1 :=
        fun w => by
          have h := dual_coord (X' w) (X w) (hX' w) (hX w) (fun i => w.embedding (f i)) (c w) (hc w)
          have e : (toMat fun i => w.embedding (f i))ᵀ = ((toMat f)ᵀ).map w.embedding := by
            ext i j; rfl
          rw [e] at h
          exact h
      have h1 : ∃ y ∈ B, (toMat f)ᵀ *ᵥ y ≠ 0 := by
        by_contra hcon
        push Not at hcon
        have : Matrix.toLin' (toMat f)ᵀ = 0 := LinearMap.ext_on hBs fun x hx => hcon x hx
        have h0 : (toMat f)ᵀ = 0 := by simpa using this
        apply hf
        funext p
        exact congrFun (congrFun h0 p.2) p.1
      have h2 := GlobalTheory.TraceDualHom.different_smul_mem_of_trace_integral K a b A B hA hB hAs hBs
        (Matrix.toLin' (toMat f)ᵀ) (fun S hS => by
          obtain ⟨φ, rfl⟩ := Matrix.toLin'.surjective S
          obtain ⟨m, hm⟩ := hint (fun p => φ p.1 p.2) hS
          refine ⟨m, ?_⟩
          rw [← hm, ← Matrix.toLin'_mul, Matrix.trace_toLin'_eq, dot_eq_trace, toMat_entries])
      have h3 : (Formalism.HN.nPl K : ℝ) * (lo / (rd * hi)) ^ 2 ≤
          ∑ w, ∑ i, ∑ j, ‖((X w)⁻¹ * ((toMat f)ᵀ).map w.embedding * X' w) i j‖ ^ 2 := by
        let ψ := (toMat f)ᵀ
        let φ := Matrix.toLin' ψ
        let A' := B.map (φ.restrictScalars (𝓞 K))
        have hA'fg : A'.FG := hB.map _
        obtain ⟨y, hyB, hy⟩ := h1
        have hA'0 : A' ≠ ⊥ := by
          intro h
          have hy' : φ y ∈ A' := ⟨y, hyB, rfl⟩
          rw [h] at hy'
          exact hy hy'
        have hB0 : B ≠ ⊥ := by
          intro h
          apply hA'0
          simp [A', h]
        have hd : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
        have hleast : lo / rd ≤ Formalism.HN.leastSize (Pi.basisFun K (Fin a)) X A' := by
          refine le_csInf ⟨_, A', le_rfl, hA'0, rfl⟩ ?_
          rintro _ ⟨N, hN, hN0, rfl⟩
          have hNfg : N.FG := Submodule.FG.of_le hA'fg hN
          have hle : differentIdeal ℤ (𝓞 K) • N ≤ A := by
            refine Submodule.smul_le.2 fun δ hδ v hv => ?_
            obtain ⟨z, hz, rfl⟩ := hN hv
            exact h2 δ hδ z hz
          have hspan := Formalism.HN.DualPolygon.twist_span_smul N _ hd
          have hne : differentIdeal ℤ (𝓞 K) • N ≠ ⊥ := by
            intro h
            rw [h] at hspan
            apply hN0
            rw [eq_bot_iff]
            intro v hv
            have hv' : v ∈ Submodule.span K (N : Set (Fin a → K)) :=
              Submodule.subset_span hv
            rw [← hspan] at hv'
            simpa using hv'
          have hsize : Formalism.HN.size (Pi.basisFun K (Fin a)) X
              (differentIdeal ℤ (𝓞 K) • N) =
                Formalism.HN.size (Pi.basisFun K (Fin a)) X N * rd := by
            have hrk : Formalism.HN.rkK (differentIdeal ℤ (𝓞 K) • N) =
                Formalism.HN.rkK N := by
              unfold Formalism.HN.rkK
              rw [hspan]
            have hnorm : (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) =
                |(discr K : ℝ)| := by
              rw [NumberField.absNorm_differentIdeal K (𝓞 K), Nat.cast_natAbs, Int.cast_abs]
            have hj : (Formalism.HN.rkK N : ℝ) ≠ 0 := by
              exact_mod_cast (Formalism.LFunctionChainParameters.slopeLatticeData.rkK_pos hN0).ne'
            unfold Formalism.HN.size rd
            rw [Formalism.LFunctionChainParameters.slopeLatticeData.ht_ideal _ X hX hNfg hd,
              hrk, hnorm, Real.mul_rpow
                (Formalism.LFunctionChainParameters.slopeLatticeData.ht_pos _ X hX hNfg).le
                (pow_nonneg (abs_nonneg (discr K : ℝ)) (Formalism.HN.rkK N)),
              ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
            congr 2
            field_simp [hn0.ne', hj]
          rw [div_le_iff₀ hrd0, ← hsize]
          exact hlow _ hle hne
        have hLpos : 0 < Formalism.HN.largestSize (Pi.basisFun K (Fin b)) X' B := by
          rw [(Formalism.HN.sizeMu K _ _ (Pi.basisFun K (Fin b)) X' hX' B hB hB0).2.2.2.2.1]
          exact Real.exp_pos _
        let opNorm := fun w => Formalism.HN.opNormAt (Pi.basisFun K (Fin b)) X'
          (Pi.basisFun K (Fin a)) X w φ
        have hgeom : lo / (rd * hi) ≤
            (∏ w, opNorm w) ^ ((1 : ℝ) / (Formalism.HN.nPl K : ℝ)) := by
          refine le_trans ?_ (Formalism.HN.sizeIneq K _ _ _ _
            (Pi.basisFun K (Fin b)) X' (Pi.basisFun K (Fin a)) X hX' hX φ B A'
            hB hA'fg le_rfl hA'0)
          rw [← div_div]
          exact div_le_div₀ ((div_pos hlo hrd0).le.trans hleast) hleast hLpos hup
        calc
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) hgeom 2) (Nat.cast_nonneg _)
          _ ≤ _ := _root_.GlobalTheory.DualBound.card_mul_geom_sq_le opNorm
            (fun w => norm_nonneg _)
          _ ≤ _ := by
            refine Finset.sum_le_sum fun w _ => ?_
            have hmatrix : LinearMap.toMatrix (Pi.basisFun K (Fin b)) (Pi.basisFun K (Fin a))
                φ = ψ := by ext i j; simp [φ]
            unfold opNorm Formalism.HN.opNormAt
            rw [hmatrix]
            exact _root_.GlobalTheory.DualBound.opNorm_sq_le_hs _
      rw [mul_pow, hss]
      refine h3.trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [hc' w, Fintype.sum_prod_type, Finset.sum_comm])
    (fun w p => T w p.1 p.2)
  refine ⟨toMat y, hy, ?_⟩
  have e1 : ∑ w, ∑ i, ∑ j, ‖(T w - (X' w)⁻¹ * (toMat y).map w.embedding * X w) i j‖ ^ 2
      = ∑ w, ∑ p : Fin b × Fin a, ‖T w p.1 p.2 -
        frameEquiv (X' w) (X w) (hX' w) (hX w) (fun j => w.embedding (y j)) p‖ ^ 2 := by
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Fintype.sum_prod_type]
    rfl
  rw [e1]
  refine hle.trans (le_of_eq ?_)
  rw [hn, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  push_cast
  set r := Real.sqrt (Formalism.HN.nPl K)
  rw [← hss]
  field_simp
