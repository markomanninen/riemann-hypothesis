module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspExpansionAtInfinityOfSomeLevel
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
theorem _root_.GlobalTheory.T.exists_cuspExpansionAtInfinity_of_someLevel : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f : ℍ → ℂ), InR ε.range f → ∃ h : HahnSeries ℚ Ω, IsExp ε f h := by
  first | exact @GlobalTheory.FN.exists_isExp | exact GlobalTheory.FN.exists_isExp | (intros; apply GlobalTheory.FN.exists_isExp <;> assumption)
