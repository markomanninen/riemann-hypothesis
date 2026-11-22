module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotForallExistsTwoLiesOverAbsNormEq
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLContinuationNeZeroOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_forall_exists_two_degree_one_primes_over : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ¬ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∃ P P' : HeightOneSpectrum (𝓞 M), P ≠ P' ∧ P.asIdeal.LiesOver v.asIdeal ∧ P'.asIdeal.LiesOver v.asIdeal ∧ Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm P'.asIdeal = Ideal.absNorm v.asIdeal := by
  exact @GlobalTheory.not_forall_exists_two_liesOver_absNorm_eq
