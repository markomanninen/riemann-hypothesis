module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionSumZetaBoundDelta
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

@[expose] public section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_sum_zeta_bound_delta : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (c : Matrix (Fin m) (Fin m) E) (r : ℝ), 1 < r → Summable (fun U : (Fin m → E) ⧸ intVec E m => (Ideal.absNorm (tor c (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r))) ∧ ∑' U : (Fin m → E) ⧸ intVec E m, (Ideal.absNorm (tor c (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) ≤ delta c * zetaR E r := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU.sum_tor | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU.sum_tor | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU.sum_tor <;> assumption)
