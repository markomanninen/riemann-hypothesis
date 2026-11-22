module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DedekindZetaEulerProductMulSubOneEntireNeZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLContinuationNeZeroOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_entire_sub_one_mul_euler_exp_ne_zero_one : ∀ (K : Type) [Field K] [NumberField K], ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → Z s = (s - 1) * Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  exact @GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire_ne_zero
