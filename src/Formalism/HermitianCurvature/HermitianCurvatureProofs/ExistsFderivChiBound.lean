module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoIntUv

@[expose] public section

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Bump

theorem dZ_contDiff {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (NF.dZ f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.1 hf).2
  have h1 : ContDiff ℝ ∞ (fun w => fderiv ℝ f w 1) := hd.clm_apply contDiff_const
  have hI : ContDiff ℝ ∞ (fun w => fderiv ℝ f w Complex.I) := hd.clm_apply contDiff_const
  show ContDiff ℝ ∞ (fun w => (1 / 2 : ℂ) * (fderiv ℝ f w 1 - Complex.I * fderiv ℝ f w Complex.I))
  exact contDiff_const.mul (h1.sub (contDiff_const.mul hI))

theorem dZb_contDiff {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (NF.dZb f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.1 hf).2
  have h1 : ContDiff ℝ ∞ (fun w => fderiv ℝ f w 1) := hd.clm_apply contDiff_const
  have hI : ContDiff ℝ ∞ (fun w => fderiv ℝ f w Complex.I) := hd.clm_apply contDiff_const
  show ContDiff ℝ ∞ (fun w => (1 / 2 : ℂ) * (fderiv ℝ f w 1 + Complex.I * fderiv ℝ f w Complex.I))
  exact contDiff_const.mul (h1.add (contDiff_const.mul hI))

end Bump

end Formalism.FourierDecayAlt.P5.HerB
