module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VerticalStatementHolds
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
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldMirabolic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaSeriesUnfoldMirabolic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_mul_norm_rpow_neg_half' : Continuous fun z : ℂ => z * ((‖z‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  first | (exact @GlobalTheory.continuous_mul_norm_rpow_neg_half) | (exact GlobalTheory.continuous_mul_norm_rpow_neg_half) | (intros; apply GlobalTheory.continuous_mul_norm_rpow_neg_half  <;> assumption)
