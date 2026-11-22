module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionOrthogonalityIntegralSolution
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
theorem _root_.GlobalTheory.T.torsion_orthogonality_integral_solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (b : E), (∀ t ∈ tor c u, σ (t : E) * b ∈ (1 : Submodule (𝓞 E) E)) → ∃ y : Fin m → 𝓞 E, y ∈ Kc c ∧ b - ∑ j, σ (u j) * (y j : E) ∈ (1 : Submodule (𝓞 E) E) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.dual_cover | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.dual_cover | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.dual_cover <;> assumption)
