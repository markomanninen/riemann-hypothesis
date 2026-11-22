module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmooth
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LactSpec

@[expose] public section

theorem UpperTheory.ConvolutionTheory.L1.lactLaws :
    UpperTheory.ConvolutionTheory.L1.LactLaws := by
  intro K _ _ n β hβ
  obtain ⟨_, _, hs, h1, hm, hc, _, _⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n β hβ
  exact ⟨fun u => (hs u).1, h1, fun u v => (hm u v).1, fun u v => (hm u v).2, fun c u => (hc c u).1⟩
