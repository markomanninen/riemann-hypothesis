module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOver
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver : ∀ E : Subring ℂ, (∀ f : ℍ → ℂ, f ∈ GlobalTheory.FN.ring E ↔ InR E f) ∧ ∀ c ∈ E, InR E fun _ => c := by
  first | exact @GlobalTheory.FN.mem_ring_iff_inR | exact GlobalTheory.FN.mem_ring_iff_inR | (intros; apply GlobalTheory.FN.mem_ring_iff_inR <;> assumption)
