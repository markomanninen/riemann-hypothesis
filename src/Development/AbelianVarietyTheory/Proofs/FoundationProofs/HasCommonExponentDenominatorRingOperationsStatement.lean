module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasCommonExponentDenominatorRingOperations
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
theorem _root_.GlobalTheory.T.hasCommonExponentDenominator_ring_operations : ∀ (Ω : Type) [Field Ω], (∀ h h' : HahnSeries ℚ Ω, Den h → Den h' → Den (h + h') ∧ Den (h - h') ∧ Den (h * h')) ∧ ∀ (r : ℚ) (c : Ω), Den (HahnSeries.single r c : HahnSeries ℚ Ω) := by
  first | exact @GlobalTheory.FN.den_ring | exact GlobalTheory.FN.den_ring | (intros; apply GlobalTheory.FN.den_ring <;> assumption)
