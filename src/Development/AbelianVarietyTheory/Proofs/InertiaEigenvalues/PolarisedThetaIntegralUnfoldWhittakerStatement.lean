module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarisedThetaIntegralUnfoldWhittaker
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate
open GlobalTheory.MirTower GlobalTheory.CuspGeneric GlobalTheory.RSJ GlobalTheory.ZUnf in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.polarisedThetaIntegral_unfold_whittaker : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure],
  ∃ c : ℝ, 0 < c ∧ ∀ (π π' : CuspSub E (m + 1)) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → π.HasCentChar ω →
    π'.HasCentChar ω' → ∀ φ φ' : GA E (m + 1) → ℂ, φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
    ∀ (N : ℕ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N → ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
      tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    ∀ (𝓕 𝓕₀ : Set (GA E (m + 1))), IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ →
      IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
    ∀ x : ℝ, 1 < x → ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ ∂μ ≠ ⊤ → ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖ₑ ∂μ ≠ ⊤ →
      IntegrableOn (GlobalTheory.ZEul.uInt φ φ' Φ N x) 𝓕₀ μ ∧
        GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = (c : ℂ) * ∫ g in 𝓕₀, GlobalTheory.ZEul.uInt φ φ' Φ N x g ∂μ := by
  intro E _ _ _ m μ _
  refine ⟨1, one_pos, ?_⟩
  intro π π' ω ω' hω hω' hπ hπ' φ φ' hφ hφ' N Φ _hN hΦs _hΦc hΦr hΦp 𝓕 𝓕₀ h𝓕 h𝓕₀ x _hx h1 h2
  have := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E (m + 1)
  have := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E (m + 1)
  have := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E (m + 1)
  obtain ⟨𝓕P, h𝓕P⟩ : ∃ 𝓕P, IsFundamentalDomain (ratMirU E (m + 1) m) 𝓕P μ := by
    have : DiscreteTopology (ratMirU E (m + 1) m) := discrete_of_le_range (Subgroup.map_le_range _ _)
    exact GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain _ μ
  have h𝓕₀' : IsFundamentalDomain (ratMirU E (m + 1) 0) 𝓕₀ μ := NE_eq_ratMirU_zero (E := E) (m := m) ▸ h𝓕₀
  obtain ⟨hc, hl, hv⟩ := GlobalTheory.T.cuspFormRapidSpan_continuous_automorphic_cuspidal E m π ω hω hπ φ hφ
  obtain ⟨hc', hl', hv'⟩ := GlobalTheory.T.cuspFormRapidSpan_continuous_automorphic_cuspidal E m π' ω' hω' hπ' φ' hφ'
  have hΦcont : Continuous Φ := hΦs.continuous
  have hG := GlobalTheory.T.archTranslatedSqrtWeightedFun_good_mirabolicTop E m φ hc hl hv Φ hΦcont hΦr (GlobalTheory.StdCharConductor.psi E)
  have hG' := GlobalTheory.T.archTranslatedSqrtWeightedFun_good_mirabolicTop E m φ' hc' hl' hv' Φ hΦcont hΦr (GlobalTheory.StdCharConductor.psi E)
  obtain ⟨hwm, hwΓ, hwU⟩ := GlobalTheory.T.lastRowCongruenceDetWeight_measurable_invariant E m N x
  have hU := GlobalTheory.MirTower.unfold_mirabolic E (m + 1) μ (GlobalTheory.StdCharConductor.psi E) (GlobalTheory.StdCharConductor.stdPsi_psi E)
    𝓕P 𝓕₀ h𝓕P h𝓕₀' (wt N x) hwm hwΓ hwU
  have hW : ∀ f : GA E (m + 1) → ℂ, Good (GlobalTheory.StdCharConductor.psi E) m f → ∀ g,
      GlobalTheory.JSW.whit f g = GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f g := fun f hf g =>
    GlobalTheory.T.globalWhittakerCoeff_eq_iteratedColumnTransform E m f hf.cont (fun γ hγ g => hf.left γ (isMir_of_mem_mirU_zero hγ) g) g
  have hd : ∫⁻ g in 𝓕P, ‖fT φ Φ g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤ := by
    rw [hU.1 _ hG]
    show ∫⁻ g in 𝓕₀, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤
    have e : ∀ g, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) =
        ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ := fun g => by rw [enorm_uInt_self hΦp, hW _ hG]
    simp only [e]
    exact h1
  have hd' : ∫⁻ g in 𝓕P, ‖fT φ' Φ g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤ := by
    rw [hU.1 _ hG']
    show ∫⁻ g in 𝓕₀, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤
    have e : ∀ g, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) =
        ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖ₑ := fun g => by rw [enorm_uInt_self hΦp, hW _ hG']
    simp only [e]
    exact h2
  obtain ⟨hI1, hI2, hEq⟩ := hU.2 _ _ hG hG' hd hd'
  have e1 : GlobalTheory.ZEul.uInt φ φ' Φ N x = fun g => GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g *
      conj (GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g) * ((wt N x g : ℝ) : ℂ) := by
    funext g
    rw [uInt_eq hΦp, hW _ hG, hW _ hG']
  have e2 : (fun g => Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)) =
      fun g => fT φ Φ g * conj (fT φ' Φ g) * ((wt N x g : ℝ) : ℂ) := funext fun g => psi_lastRow_eq hΦp φ φ' N x g
  have hfin : ∫⁻ g in 𝓕P, ‖Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)‖ₑ ∂μ ≠ ⊤ := by
    rw [show (fun g => ‖Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)‖ₑ) =
      fun g => ‖fT φ Φ g * conj (fT φ' Φ g) * ((wt N x g : ℝ) : ℂ)‖ₑ from funext fun g => by rw [psi_lastRow_eq hΦp]]
    exact hI1.2.ne
  refine ⟨by rw [e1]; exact hI2, ?_⟩
  have hUnfold := GlobalTheory.ZUnfTheta.zint_eq_mirabolic E m μ 𝓕 𝓕P h𝓕 h𝓕P
    φ φ' hc.measurable hc'.measurable hl hl' N Φ hΦcont x hfin
  rw [hUnfold, e2, Complex.ofReal_one, one_mul, e1]
  exact hEq
