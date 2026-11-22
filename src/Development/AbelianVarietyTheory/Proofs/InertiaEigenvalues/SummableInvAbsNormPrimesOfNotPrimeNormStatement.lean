module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableInvAbsNormPrimesOfNotPrimeNorm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLContinuationNeZeroOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_inv_absNorm_primes_of_not_prime_norm : ∀ (K : Type) [Field K] [NumberField K], Summable fun P : {P : HeightOneSpectrum (𝓞 K) // ¬ (Ideal.absNorm P.asIdeal).Prime} => ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ)⁻¹ := by
  exact @GlobalTheory.summable_inv_absNorm_of_not_prime
