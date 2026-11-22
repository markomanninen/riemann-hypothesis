module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqUniformizerCharacterMulResidueCardPowEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntIndMemSB

@[expose] public section

open MeasureTheory Matrix ValuativeRel

open GlobalTheory GlobalTheory.HeisUnit in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normSq_uniformizer_character_mul_residueCard_pow_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ},
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C)) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Tr C φ y * (starRingEnd ℂ) (Tr C φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∀ φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), ι φ0 = GlobalTheory.HeisUnit.intInd k n d → φ0 ≠ 0 →
    ∀ (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (i0 : Fin n),
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ T T' : Fin d → GlobalTheory.SplitFlip.Res (k := k) 1, T ≠ T' →
      ∫ y, Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T') φ0 y) ∂μ = 0) →
    ‖(χ ϖ : ℂ)‖ ^ 2 * (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d = 1 := by
  intro k _ _ _ _ n d ι hinj Tr hTr hTrIso S hS hSiso χ hχ φ0 hφ0 hι0 hne ϖ hϖ i0 horth
  classical
  set F := ∑ T : Fin d → SplitFlip.Res (k := k) 1, Tr (cosetRep ϖ i0 T) φ0 with hF
  have hFSB : F ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k) := Submodule.sum_mem _ fun T _ => (hTr _ φ0 hφ0).1
  have hSg : S (diagAt ϖ i0) φ0 = (χ ϖ : ℂ) • F := by
    apply hinj (hS _ φ0 hφ0) (Submodule.smul_mem _ _ hFSB)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hχ _ φ0 hφ0, map_smul, map_sum, det_diagAt, hι0]
    funext Y
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, (hTr _ φ0 hφ0).2, hι0]
    have hIntInd (M : Matrix (Fin n) (Fin d) k) :
        intInd k n d M = if ∀ i j, M i j ∈ 𝒪[k] then 1 else 0 := by
      simp only [intInd, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    have hSubMem (y : k) (t : SplitFlip.Res (k := k) 1) :
        y - (ϖ : k)⁻¹ * ((Quotient.out t : 𝒪[k]) : k) ∈ 𝒪[k] ↔
          ∃ h : (ϖ : k) * y ∈ 𝒪[k], t = Ideal.Quotient.mk _ ⟨(ϖ : k) * y, h⟩ := by
      have ht : t = Ideal.Quotient.mk _ (Quotient.out t) := (Quotient.out_eq t).symm
      set a := Quotient.out t
      have hϖ0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
      constructor
      · intro hc
        have hy : (ϖ : k) * y = ϖ * (y - (ϖ : k)⁻¹ * a) + a := by field_simp; ring
        have hmem : (ϖ : k) * y ∈ 𝒪[k] := hy ▸ add_mem (mul_mem hϖ.mem hc) a.2
        refine ⟨hmem, ?_⟩
        rw [ht, Ideal.Quotient.eq, pow_one, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton']
        refine ⟨-⟨_, hc⟩, Subtype.ext ?_⟩
        push_cast
        field_simp
        ring
      · rintro ⟨h, e⟩
        have e' := ht.symm.trans e
        rw [Ideal.Quotient.eq, pow_one, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at e'
        obtain ⟨c, hc⟩ := e'
        have hc' : (c : k) * ϖ = a - ϖ * y := by simpa using congrArg Subtype.val hc
        have hinv : (ϖ : k)⁻¹ * ϖ = 1 := inv_mul_cancel₀ hϖ0
        have : y - (ϖ : k)⁻¹ * a = -(c : k) := by
          linear_combination (ϖ : k)⁻¹ * hc' - (y + c) * hinv
        rw [this]
        exact neg_mem c.2
    have hDiag :
        intInd k n d ((diagAt ϖ i0).valᵀ * Y) =
          ∑ T : Fin d → SplitFlip.Res (k := k) 1, intInd k n d (Y + cosetRep ϖ i0 T) := by
      have hL : ∀ i j, ((diagAt ϖ i0).valᵀ * Y) i j = (if i = i0 then (ϖ : k) else 1) * Y i j := by
        intro i j
        rw [diagAt_val, diagonal_transpose, diagonal_mul]
      have hR : ∀ (T : Fin d → SplitFlip.Res (k := k) 1) i j, (Y + cosetRep ϖ i0 T) i j =
          if i = i0 then Y i j - (ϖ : k)⁻¹ * ((Quotient.out (T j) : 𝒪[k]) : k) else Y i j := by
        intro T i j
        simp only [cosetRep, Matrix.add_apply, Matrix.of_apply]
        split_ifs <;> ring
      by_cases hQR : (∀ i j, i ≠ i0 → Y i j ∈ 𝒪[k]) ∧ ∀ j, (ϖ : k) * Y i0 j ∈ 𝒪[k]
      · obtain ⟨hQ, hRR⟩ := hQR
        let T0 : Fin d → SplitFlip.Res (k := k) 1 := fun j => Ideal.Quotient.mk _ ⟨_, hRR j⟩
        have hl : intInd k n d ((diagAt ϖ i0).valᵀ * Y) = 1 := by
          rw [hIntInd, ite_eq_left]
          intro i j
          rw [hL]
          split_ifs with h
          · subst h; exact hRR j
          · rw [one_mul]; exact hQ i j h
        have hs : ∀ T, intInd k n d (Y + cosetRep ϖ i0 T) = if T = T0 then 1 else 0 := by
          intro T
          rw [hIntInd]
          by_cases hT : T = T0
          · rw [ite_eq_left hT, ite_eq_left]
            intro i j
            rw [hR]
            split_ifs with h
            · subst h; exact (hSubMem _ _).2 ⟨hRR j, by rw [hT]⟩
            · exact hQ i j h
          · rw [ite_eq_right hT, ite_eq_right]
            intro hm
            apply hT
            funext j
            have := hm i0 j
            rw [hR, ite_eq_left rfl] at this
            obtain ⟨_, e⟩ := (hSubMem _ _).1 this
            exact e
        rw [hl, Finset.sum_congr rfl (fun T _ => hs T), Finset.sum_ite_eq']
        simp
      · have hl : intInd k n d ((diagAt ϖ i0).valᵀ * Y) = 0 := by
          rw [hIntInd, ite_eq_right]
          intro hm
          refine hQR ⟨fun i j h => ?_, fun j => ?_⟩
          · have := hm i j; rwa [hL, ite_eq_right h, one_mul] at this
          · have := hm i0 j; rwa [hL, ite_eq_left rfl] at this
        rw [hl]
        symm
        apply Finset.sum_eq_zero
        intro T _
        rw [hIntInd, ite_eq_right]
        intro hm
        refine hQR ⟨fun i j h => ?_, fun j => ?_⟩
        · have := hm i j; rwa [hR, ite_eq_right h] at this
        · have := hm i0 j
          rw [hR, ite_eq_left rfl] at this
          exact ((hSubMem _ _).1 this).1
    rw [hDiag]

  let _ : MeasurableSpace (Fin n × Fin d → k) := borel _
  have _ : BorelSpace (Fin n × Fin d → k) := ⟨rfl⟩
  let μ : Measure (Fin n × Fin d → k) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  have hiso := hSiso (diagAt ϖ i0) φ0 hφ0 μ hμ
  rw [hSg] at hiso
  simp only [Pi.smul_apply, smul_eq_mul, eNorm_mul, mul_pow] at hiso
  rw [lintegral_const_mul' _ _ (by simp [eNorm_eq_nnNorm])] at hiso
  obtain ⟨hFtop, hFint, -, hFi⟩ := GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ F hFSB
  obtain ⟨h0top, h0int, h0ne, -⟩ := GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ φ0 hφ0
  have hN0 : (∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h0ne hne, h0top⟩
  have hint : ∀ T T' : Fin d → SplitFlip.Res (k := k) 1, Integrable (fun y => Tr (cosetRep ϖ i0 T) φ0 y *
      (starRingEnd ℂ) (Tr (cosetRep ϖ i0 T') φ0 y)) μ := fun T T' =>
    (GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ _ (hTr _ φ0 hφ0).1).2.2.2 _ (hTr _ φ0 hφ0).1
  have hsum : ∫ y, F y * (starRingEnd ℂ) (F y) ∂μ =
      (Fintype.card (Fin d → SplitFlip.Res (k := k) 1) : ℂ) * ∫ y, φ0 y * (starRingEnd ℂ) (φ0 y) ∂μ := by
    have hpt : ∀ y, F y * (starRingEnd ℂ) (F y) = ∑ T : Fin d → SplitFlip.Res (k := k) 1, ∑ T' : Fin d → SplitFlip.Res (k := k) 1,
        Tr (cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (cosetRep ϖ i0 T') φ0 y) := by
      intro y
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hF, Finset.sum_apply, map_sum, Finset.sum_mul_sum]
    simp_rw [hpt]
    rw [integral_finsetSum _ fun T _ => integrable_finsetSum _ fun T' _ => hint T T']
    simp_rw [integral_finsetSum _ fun T' _ => hint _ T']
    rw [Finset.card_univ.symm, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.sum_eq_single T (fun T' _ hT' => horth μ hμ T T' (Ne.symm hT')) (fun h => absurd (Finset.mem_univ _) h)]
    exact hTrIso μ hμ _ φ0 hφ0 φ0 hφ0
  rw [hFint, h0int] at hsum
  have hLF : (∫⁻ y, ‖F y‖ₑ ^ 2 ∂μ).toReal =
      (Fintype.card (Fin d → SplitFlip.Res (k := k) 1) : ℝ) * (∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ).toReal := by
    exact_mod_cast hsum
  have hiso' := congrArg ENNReal.toReal hiso
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_eNorm, hLF] at hiso'
  have hcard : (Fintype.card (Fin d → SplitFlip.Res (k := k) 1) : ℝ) = (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_eq_nat_card]
    have : Nat.card (SplitFlip.Res (k := k) 1) = GlobalTheory.SplitWeil.resCard k :=
      Nat.card_congr (Ideal.quotEquivOfEq (pow_one 𝓂[k])).toEquiv
    rw [this]; push_cast; ring
  rw [hcard] at hiso'
  apply mul_right_cancel₀ hN0
  linear_combination hiso'
