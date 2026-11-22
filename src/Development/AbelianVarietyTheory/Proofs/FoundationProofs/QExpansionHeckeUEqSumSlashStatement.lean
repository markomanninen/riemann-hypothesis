module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionHeckeUEqSumSlash
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansion_heckeU_eq_sum_slash : ∀ (k l : ℕ) (a : ℕ → ℂ), 1 ≤ k → 0 < l → PolyB a → PolyB (Uo l a) ∧ ∀ τ : ℍ, qs (Uo l a) τ = ∑ j : Fin l, slz k (repU l j) (qs a) τ := by
  first | exact @GlobalTheory.EisM.Uo_qs_sum_slz | exact GlobalTheory.EisM.Uo_qs_sum_slz | (intros; apply GlobalTheory.EisM.Uo_qs_sum_slz <;> assumption)
