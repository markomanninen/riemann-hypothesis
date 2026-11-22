module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieModelFiniteBaseChange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGlobalWhittakerCoefficientGLAdeles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsuppVanishingOnEquivComplProd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenAdelicUnipotentTimesIntegralOutsideSet
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_theta_below_det_one : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (π' : CuspSub E (m + 1)), π'.IsUnitary →
    ∀ φ' ∈ GlobalTheory.JSW.mspanR π', ∀ G ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)),
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕 : Set (GA E (m + 1))),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → ∀ x : ℝ, 1 < x →
      ∫⁻ g in 𝓕 ∩ {g | GlobalTheory.RSnm.detAbs g ≤ 1}, ‖φ' g‖ₑ ^ 2 * (∑' ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0}, ‖G (Matrix.vecMul (fun j => algebraMap E (Ad E) (ξ.1 j)) g.val)‖ₑ) * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ x) ∂μ ≠ ⊤ := by
  intro E _ _ _ m π' hπ φ' hφ G hG μ _ 𝓕 h𝓕 x hx
  have hbound := GlobalTheory.ThetaSqLow.exists_bound hπ hφ hG
  obtain ⟨C, hC⟩ := hbound
  have hi : IntegrableOn (fun g : GA E (m + 1) => GlobalTheory.RSnm.detAbs g ^ (x - 1))
      (𝓕 ∩ {g | GlobalTheory.RSnm.detAbs g ≤ 1}) μ :=
    GlobalTheory.T.integrableOn_absDet_rpow_le_one_fundamentalDomain
      E (m + 1) m.succ_pos μ 𝓕 h𝓕 (x - 1) (by linarith)
  refine ne_top_of_le_ne_top (hi.const_mul C).2.ne (lintegral_mono fun g => ?_)
  have hδ := GlobalTheory.RSnm.detAbs_pos g
  refine (mul_le_mul_left (hC g) _).trans ?_
  rw [mul_comm, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), Real.eNorm_eq_ofReal_abs]
  refine ENNReal.ofReal_le_ofReal (le_trans (le_of_eq ?_) (le_abs_self _))
  beta_reduce
  rw [Real.rpow_sub_one hδ.ne']
  ring
