module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSturmBoundIsModularFormCoeffSeq
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sturmBound_isModularFormCoeffSeq : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N), 0 < L → N ∣ L → ∃ B : ℕ, ∀ a, MF k L (ch ε) a → (∀ n < B, a n = 0) → a = 0 := by
  first | exact @GlobalTheory.EisM.sturm_coef_zero | exact GlobalTheory.EisM.sturm_coef_zero | (intros; apply GlobalTheory.EisM.sturm_coef_zero <;> assumption)
