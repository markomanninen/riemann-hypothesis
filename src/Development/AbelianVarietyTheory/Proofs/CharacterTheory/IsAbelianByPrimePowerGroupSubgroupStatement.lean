module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsAbelianByPrimePowerGroupSubgroup
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianByPrimePowerGroup_subgroup : ∀ (G : Type) [Group G] (T : Subgroup G), AbByP G → AbByP T := by
  first | exact @GlobalTheory.BI.AbByP.subgroup | exact GlobalTheory.BI.AbByP.subgroup | (intros; apply GlobalTheory.BI.AbByP.subgroup <;> assumption)
