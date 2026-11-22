module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeVOperatorRaisesLevel
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffHeckeVOperator_raises_level : ∀ (k L l : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ), 0 < l → (MF k L χ a → MF k (L * l) χ (Vo l a)) ∧ (CF k L χ a → CF k (L * l) χ (Vo l a)) := by
  first | exact @GlobalTheory.Vo_level | exact GlobalTheory.Vo_level | (intros; apply GlobalTheory.Vo_level <;> assumption)
