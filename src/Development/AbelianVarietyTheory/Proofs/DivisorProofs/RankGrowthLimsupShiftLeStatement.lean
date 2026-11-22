module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLimsupShiftLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero

@[expose] public section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankGrowthLimsup_shift_le : ∀ (D e : ℕ) (r : ℕ → ℕ∞), growth D (fun k => r (k + e)) ≤ growth D r := by
  first | exact @GlobalTheory.GrowthShift.growth_shift_le | exact GlobalTheory.GrowthShift.growth_shift_le | (intros; apply GlobalTheory.GrowthShift.growth_shift_le <;> assumption)
