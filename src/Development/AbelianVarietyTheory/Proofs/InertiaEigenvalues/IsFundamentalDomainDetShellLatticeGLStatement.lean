module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFundamentalDomainDetShellLatticeGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormRsHatLeConst
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralUpperMspan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousIntegralOfCompact
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralRsHatZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFundamentalDomain_det_shell_latticeGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (latticeGL E a) (𝓕 ∩ {g | Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) < (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ := by
  first | (exact @GlobalTheory.ShellFD.isFundamentalDomain_shell) | (exact GlobalTheory.ShellFD.isFundamentalDomain_shell) | (intros; apply GlobalTheory.ShellFD.isFundamentalDomain_shell  <;> assumption)
