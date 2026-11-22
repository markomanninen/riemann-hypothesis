module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeRowDifferenceSummableBound
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisensteinLattice_rowDifference_summable_bound : ∀ j L : ℕ, 2 ≤ j → 0 < L → ∃ (C : ℝ) (A : ℕ), ∀ τ : ℍ, ∃ u : ℤ × ℤ → ℝ, Summable u ∧ ∑' x, u x ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹) ∧ ∀ (s : ℝ) (x : ℤ × ℤ), 0 ≤ s → s ≤ 1 → ‖dif L (0, 1) (fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x‖ ≤ u x := by
  first | exact @GlobalTheory.RowBd.rowbd | exact GlobalTheory.RowBd.rowbd | (intros; apply GlobalTheory.RowBd.rowbd <;> assumption)
