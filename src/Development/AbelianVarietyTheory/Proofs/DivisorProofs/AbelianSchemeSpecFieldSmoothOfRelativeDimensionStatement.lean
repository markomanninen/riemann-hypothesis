module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSpecFieldSmoothOfRelativeDimension
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et
open scoped TensorProduct DirectSum
open ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_specField_smoothOfRelativeDimension : ∀ (k : Type) [Field k] (A : Over (Spec (CommRingCat.of k))) [GrpObj A], IsAbelianScheme A → ∃ g : ℕ, SmoothOfRelativeDimension g A.hom := by
  first | (exact @GlobalTheory.AbFieldDim.exists_smoothOfRelativeDimension) | (exact GlobalTheory.AbFieldDim.exists_smoothOfRelativeDimension) | (intros; apply GlobalTheory.AbFieldDim.exists_smoothOfRelativeDimension  <;> assumption)
