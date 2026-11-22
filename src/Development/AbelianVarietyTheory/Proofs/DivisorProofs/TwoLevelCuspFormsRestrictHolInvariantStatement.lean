module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsRestrictHolInvariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LactMemDomOfIsom

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoLevelCuspForms_restrict_holInvariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ), F ∈ M.SS la → M.res F ∈ HA M := by
  first | exact @GlobalTheory.CuspEmb.res_mem_HA | exact GlobalTheory.CuspEmb.res_mem_HA | (intros; apply GlobalTheory.CuspEmb.res_mem_HA <;> assumption)
