module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormGammaOneOfCoeffSeq
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularForm_gammaOne_of_coeffSeq : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), 0 < L → N ∣ L → MF k L (ch ε) a → ∃ f : ModularForm (Gamma1 L) (k : ℤ), ⇑f = qs a := by
  first | exact @GlobalTheory.EisM.modularForm_gammaOne_of_MF | exact GlobalTheory.EisM.modularForm_gammaOne_of_MF | (intros; apply GlobalTheory.EisM.modularForm_gammaOne_of_MF <;> assumption)
