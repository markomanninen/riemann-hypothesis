module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsMulMemAddWeight
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LactMemDomOfIsom

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoLevelCuspForms_mul_mem_add_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la mu : Wt M.Ψ r) (F G : C → Frame M.Ψ r → ℂ), F ∈ M.SS la → G ∈ M.SS mu → F * G ∈ M.SS (la + mu) := by
  first | exact @GlobalTheory.CuspEmb.twoLevels_mul_mem_SS | exact GlobalTheory.CuspEmb.twoLevels_mul_mem_SS | (intros; apply GlobalTheory.CuspEmb.twoLevels_mul_mem_SS <;> assumption)
