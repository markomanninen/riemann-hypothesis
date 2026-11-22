module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockSeriesZetaBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumCompBoundedFibresLeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndexStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LamIsLatticeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeQuotientTorsionNonzeroStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionCardLeAbsNormPowStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeOfDualPairingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorIndexBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorNormQuadraticExtensionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPrincipalElementNormBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativeNormCmAbsNormStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmConjugationPropertiesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionOrthogonalityIntegralSolutionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockMatrixMultiplicativeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockQuotientInjectionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionNormZetaBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockLowerBoundTorsionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionSumZetaBoundDeltaStatement

@[expose] public section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_block_series_zeta_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (s : ℝ), 1 < s → Summable (fun D : FQ F => (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s)) ∧ ∑' D : FQ F, (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) ≤ C * zetaR F (2 * s - 1) * (delta c : ℝ) ^ (-s) * (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD.sum_delta_le | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD.sum_delta_le | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD.sum_delta_le <;> assumption)
