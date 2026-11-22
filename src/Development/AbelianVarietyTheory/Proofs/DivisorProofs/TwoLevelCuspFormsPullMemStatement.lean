module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsPullMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LactMemDomOfIsom

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoLevelCuspForms_pull_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ) (h : U), F ∈ M.SS la → M.pull h F ∈ M.SS la := by
  first | exact @GlobalTheory.CuspEmb.pull_mem_SS | exact GlobalTheory.CuspEmb.pull_mem_SS | (intros; apply GlobalTheory.CuspEmb.pull_mem_SS <;> assumption)
