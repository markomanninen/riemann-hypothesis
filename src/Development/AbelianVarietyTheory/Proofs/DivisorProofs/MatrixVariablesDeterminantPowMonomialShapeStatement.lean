module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixVariablesDeterminantPowMonomialShape
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.RootStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.FactorialWeightedSumBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.OmBStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame

@[expose] public section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixVariablesDeterminantPow_monomial_shape : ∀ (C : Type) [Field C] [CharZero C] (i c : ℕ), (detPow C i c).IsHomogeneous (i * c) ∧ (∀ α, ∃ n : ℤ, (detPow C i c).coeff α = n) ∧ (detPow C i c).coeff (∑ a : Fin i, Finsupp.single ⟨a, a⟩ c) = 1 ∧ ∀ α ∈ (detPow C i c).support, (∀ a : Fin i, ∑ b : Fin i, α ⟨b, a⟩ = c) ∧ (∀ b : Fin i, ∑ a : Fin i, α ⟨b, a⟩ = c) := by
  first | exact @GlobalTheory.DetPowShape.detPow_shape | exact GlobalTheory.DetPowShape.detPow_shape | (intros; apply GlobalTheory.DetPowShape.detPow_shape <;> assumption)
