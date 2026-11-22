module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCommonLevelSpanMultiple
public import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Klm

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_level_span_multiple : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (K : ℕ) {ι : Type} [Fintype ι] (y : ι → X.Kl l), 0 < K → ∃ M : ℕ, 0 < M ∧ K ∣ M ∧ ∀ i, y i ∈ X.Lev l M := by
  first | exact @GlobalTheory.KZ.Tower.exists_lev_family | exact GlobalTheory.KZ.Tower.exists_lev_family | (intros; apply GlobalTheory.KZ.Tower.exists_lev_family <;> assumption)
