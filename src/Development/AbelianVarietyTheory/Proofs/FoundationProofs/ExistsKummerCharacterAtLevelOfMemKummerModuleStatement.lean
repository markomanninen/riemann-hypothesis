module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerCharacterAtLevelOfMemKummerModule
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kummerCharacterAtLevel_of_mem_kummerModule : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], JHol X → ∀ (n : ℕ), ∀ x ∈ X.A l, ∃ χ : SL(2, ℤ) → ZMod (l ^ n), Kum X l n x χ := by
  first | exact @GlobalTheory.KZ.H3.exists_kum_of_mem_A | exact GlobalTheory.KZ.H3.exists_kum_of_mem_A | (intros; apply GlobalTheory.KZ.H3.exists_kum_of_mem_A <;> assumption)
