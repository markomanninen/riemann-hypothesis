module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffComposedPartialDerivListOfNodup
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockSymApply
public import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockGraph

@[expose] public section

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_composedPartialDerivList_of_nodup : ∀ {σ : Type} [DecidableEq σ] (l : List σ), l.Nodup → ∀ (m : σ →₀ ℕ), (∀ v ∈ l, m v = 0) → ∀ (G : MvPolynomial σ ℂ), AddMonoidAlgebra.coeff (dList l G) m = AddMonoidAlgebra.coeff G (m + (l.map fun v => Finsupp.single v 1).sum) := by
  first | exact @GlobalTheory.CayleyBlock.coeff_dList_of_nodup | exact GlobalTheory.CayleyBlock.coeff_dList_of_nodup | (intros; apply GlobalTheory.CayleyBlock.coeff_dList_of_nodup <;> assumption)
