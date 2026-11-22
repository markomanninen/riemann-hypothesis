module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffRenameCayleyBlockSymbolEmbeddi
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockSymApply
public import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockGraph

@[expose] public section

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeFormCoeff_rename_cayleyBlockSymbolEmbedding : ∀ {p q : ℕ} (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q) (G : MvPolynomial (Fin q × Fin p × Fin p) ℂ), GlobalTheory.GoodMetric.topCoeff (rename (blockEmb h1) G) = ∑ τ : Fin q → Equiv.Perm (Fin p), (sgnProd τ : ℂ) * AddMonoidAlgebra.coeff G (blockGraph τ) := by
  first | exact @GlobalTheory.CayleyBlock.topCoeff_rename_blockEmb | exact GlobalTheory.CayleyBlock.topCoeff_rename_blockEmb | (intros; apply GlobalTheory.CayleyBlock.topCoeff_rename_blockEmb <;> assumption)
