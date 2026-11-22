module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUpperLevelSubgroupComponent
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_upperLevel_subgroup_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (c : C), ∃ G : Subgroup (GL (Fin r) E), (∀ β, β ∈ G ↔ β ∈ M.upper c) ∧ (M.comp c).Γ ≤ G := by
  first | exact @GlobalTheory.upperLevel_isSubgroup | exact GlobalTheory.upperLevel_isSubgroup | (intros; apply GlobalTheory.upperLevel_isSubgroup <;> assumption)
