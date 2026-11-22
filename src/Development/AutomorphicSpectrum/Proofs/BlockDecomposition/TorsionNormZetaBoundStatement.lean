module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionNormZetaBound
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

@[expose] public section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_norm_zeta_bound : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (L : Submodule (𝓞 K) (Fin m → K)), IsLat L → ∀ r : ℝ, 1 < r → Summable (fun x : (Fin m → K) ⧸ L => (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r))) ∧ ∑' x : (Fin m → K) ⧸ L, (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r)) ≤ zetaR K r := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.sum_torsion | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.sum_torsion | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.sum_torsion <;> assumption)
