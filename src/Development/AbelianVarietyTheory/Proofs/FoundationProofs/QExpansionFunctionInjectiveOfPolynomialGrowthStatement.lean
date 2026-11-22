module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionFunctionInjectiveOfPolynomialGrowth
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansionFunction_injective_of_polynomialGrowth : ∀ a b : ℕ → ℂ, PolyB a → PolyB b → qs a = qs b → a = b := by
  first | exact @GlobalTheory.EisM.qs_injective | exact GlobalTheory.EisM.qs_injective | (intros; apply GlobalTheory.EisM.qs_injective <;> assumption)
