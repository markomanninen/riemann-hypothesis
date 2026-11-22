module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

@[expose] public section

open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completed_laurent_isDVR_statement : ∀ (p : ℕ) [Fact p.Prime], ∃ _ : IsDomain (O0 p), IsDiscreteValuationRing (O0 p) ∧ Irreducible (p : O0 p) := by
  first | exact @GlobalTheory.K5.completed_laurent_isDVR | exact GlobalTheory.K5.completed_laurent_isDVR | (intros; apply GlobalTheory.K5.completed_laurent_isDVR <;> assumption)
