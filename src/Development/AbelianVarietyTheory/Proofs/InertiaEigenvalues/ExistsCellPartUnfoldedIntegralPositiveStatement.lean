module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCellPartUnfoldedIntegralPositive
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRankinSelbergSchurTermFinsuppEulerProductStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
open GlobalTheory.CellBump GlobalTheory.CellDec GlobalTheory.RSJ in
set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cellPart_unfoldedIntegral_positive : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ) (φ : GA E (m + 1) → ℂ)
    (N : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (Φ : (Fin (m + 1) → Cinf E) → ℂ),
    0 < N → (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) →
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) →
    Continuous Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) → Φ (Pi.single (Fin.last m) 1) ≠ 0 →
    Continuous (GlobalTheory.JSW.whit φ) →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, GlobalTheory.JSW.whit φ (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ g) →
    b 1 = 1 → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) →
    (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit φ p = b p) →
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E (m + 1))),
    IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
    ∃ f t : GA E (m + 1) → ℝ, Measurable f ∧ Measurable t ∧ (∀ g, 0 ≤ f g) ∧ IntegrableOn f 𝓕₀ μ ∧
      0 < ∫ g in 𝓕₀, f g ∂μ ∧ (∃ R : ℝ, ∀ g, f g ≠ 0 → |t g| ≤ R) ∧
      (∀ g ∉ GlobalTheory.CellDec.C0 E (m + 1) S, f g = 0) ∧
      (∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, GlobalTheory.ZEul.uInt φ φ Φ N 0 g = (f g : ℂ)) ∧
      ∀ (x : ℝ) (g : GA E (m + 1)), (GlobalTheory.RSJ.detPow E (m + 1) x g : ℂ) = Complex.exp (x * t g) := by
  intro E _ _ _ m S b φ N J Φ hN0 hJ hNJ hΦ hΦc hs hΦr hΦ1 hWc hN hK hb1 hb hW μ _ 𝓕₀ h𝓕
  have hO := isOpen_adelicUnipotentTimesIntegralOutsideSet E (m + 1) S
  have hre := fun g => uInt_self_zero hΦr φ N g
  have hc : Continuous (GlobalTheory.ZEul.uInt φ φ Φ N 0) := continuous_uInt hN0 hWc hWc hΦ hs 0
  have hBc : Continuous fun g => (GlobalTheory.ZEul.uInt φ φ Φ N 0 g).re := Complex.continuous_re.comp hc
  obtain ⟨K, hKc, hKs⟩ := exists_compact_support hJ hNJ hΦc hs hN hK hb hW

  have hS1 : (1 : GA E (m + 1)) ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) :=
    ⟨fun w _ => map_one _, fun j => by simp [Matrix.one_apply, eq_comm]⟩
  have hy1 : (fun i => pInf E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)) = Pi.single (Fin.last m) 1 := by
    funext i
    by_cases h : i = Fin.last m
    · subst h; simp [GlobalTheory.ZEul.lastRow]
    · simp [GlobalTheory.ZEul.lastRow, Matrix.one_apply_ne (Ne.symm h), h]
  have hyl : (Pi.single (Fin.last m) 1 : Fin (m + 1) → Cinf E) = GlobalTheory.RSJ.Model.eLast (Cinf E) (m + 1) := by
    funext i; rw [single_last_eq]; rfl
  have hf1 : indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)) = 1 := by
    unfold indN
    refine ite_eq_left fun i => ?_
    have : GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i) = if (i : ℕ) + 1 = m + 1 then 1 else 0 := by
      rw [← single_last_eq (R := Af E)]
      by_cases h : i = Fin.last m
      · subst h; simp [GlobalTheory.ZEul.lastRow]
      · simp [GlobalTheory.ZEul.lastRow, Matrix.one_apply_ne (Ne.symm h), h]
    show GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i) - _ ∈ _
    rw [this, sub_self]
    exact ⟨0, fun v => zero_mem _, by simp⟩
  have hB1 : 0 < (GlobalTheory.ZEul.uInt φ φ Φ N 0 1).re := by
    have e : GlobalTheory.ZEul.uInt φ φ Φ N 0 1 = Φ (Pi.single (Fin.last m) 1) := by
      change GlobalTheory.JSW.whit φ (1 * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i))) *
        conj (GlobalTheory.JSW.whit φ (1 * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)))) *
        Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)) *
        indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)) *
        (detPow E (m + 1) 0 1 : ℂ) = _
      rw [hf1, hy1, hyl, GlobalTheory.RSJ.Model.secInv_eLast, map_one, one_mul, hW 1 hS1, hb1, detPow_eq, ← hyl]
      simp
    rw [e]
    refine lt_of_le_of_ne (hΦr _).1 fun h => hΦ1 (Complex.ext h.symm (hΦr _).2)

  obtain ⟨hpos, -⟩ := GlobalTheory.RSLocalPart.lintegral_cell_pos_lt_top_continuous E (m + 1) μ S 𝓕₀ h𝓕
    (fun _ g => (GlobalTheory.ZEul.uInt φ φ Φ N 0 g).re) (hBc.comp continuous_snd) (fun _ g => (hre g).2) (fun _ => hB1)
    (fun _ u hu g => by simp only [uInt_unip_mul hN Φ N 0 hu g])
    ⟨K, hKc, fun _ g hg h0 => hKs g hg fun h => h0 (by rw [h, Complex.zero_re])⟩
  obtain ⟨hlpos, hltop⟩ := hpos 0
  have hIB : IntegrableOn (fun g => (GlobalTheory.ZEul.uInt φ φ Φ N 0 g).re) (𝓕₀ ∩ C0 E (m + 1) S) μ :=
    ⟨hBc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun g => (hre g).2)).2 hltop⟩

  set t : GA E (m + 1) → ℝ := fun g => GlobalTheory.Mem.Chr.CharModel.logNorm E (Matrix.GeneralLinearGroup.det g) with ht
  have htc : Continuous t := (GlobalTheory.Mem.Chr.CharModel.continuous_logNorm E).comp Matrix.GeneralLinearGroup.continuous_det
  have htu : ∀ u ∈ NA E (m + 1), ∀ g, t (u * g) = t g := fun u hu g => by
    simp only [ht, map_mul, show Matrix.GeneralLinearGroup.det u = 1 from Units.ext (GlobalTheory.RSLocalPart.det_eq_one hu),
      one_mul]
  obtain ⟨R, hR⟩ := hKc.exists_bound_of_continuousOn htc.continuousOn
  refine ⟨(C0 E (m + 1) S).indicator fun g => (GlobalTheory.ZEul.uInt φ φ Φ N 0 g).re, t,
    hBc.measurable.indicator hO.measurableSet, htc.measurable,
    fun g => Set.indicator_nonneg (fun g _ => (hre g).2) g, ?_, ?_, ⟨R, fun g hg => ?_⟩,
    fun g hg => Set.indicator_of_notMem hg _, fun g hg => ?_, fun x g => ?_⟩
  · unfold IntegrableOn
    rw [integrable_indicator_iff hO.measurableSet]
    unfold IntegrableOn
    rw [Measure.restrict_restrict hO.measurableSet, Set.inter_comm]
    exact hIB
  · rw [integral_indicator hO.measurableSet, Measure.restrict_restrict hO.measurableSet, Set.inter_comm,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun g => (hre g).2) hBc.aestronglyMeasurable]
    exact ENNReal.toReal_pos hlpos.ne' hltop.ne
  · have hgC : g ∈ C0 E (m + 1) S := by
      by_contra h
      exact hg (Set.indicator_of_notMem h _)
    rw [Set.indicator_of_mem hgC] at hg
    obtain ⟨u, hu, hk⟩ := hKs g hgC fun h => hg (by rw [h, Complex.zero_re])
    have := hR _ hk
    rwa [htu u hu, Real.norm_eq_abs] at this
  · rw [Set.indicator_of_mem hg]
    exact (hre g).1
  · rw [detPow_eq, Complex.ofReal_exp]
    push_cast
    rfl
