module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MonomialBlockSupplyBothTypings
public import Formalism.LocalToGlobal.CharacterGerms.ContentLargeFromSupplies
public import Formalism.LocalToGlobal.CharacterGerms.ContentZeroAt
public import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective

@[expose] public section

open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomialBlock_supply_both_typings : MONSupply ∧ RF.MONSupply := by
  first | exact @GlobalTheory.MonBlock.monSupply | exact GlobalTheory.MonBlock.monSupply | (intros; apply GlobalTheory.MonBlock.monSupply <;> assumption)
