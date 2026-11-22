module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGaloisExtensionOfEmbedding
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisAction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSubLeOfNear

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_extension_of_embedding : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l),
    ∃ g : GQ l, ∀ x : ↥K.1, g (x : Om l) = μ x := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.exists_gal_extending_embedding | exact GlobalTheory.CompanionTheory.LTPer.Tilt.exists_gal_extending_embedding | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.exists_gal_extending_embedding <;> assumption)
