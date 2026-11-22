module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.OddLevelBlockBoundAttained
public import Formalism.LocalToGlobal.CharacterGerms.ContentLargeFromSupplies
public import Formalism.LocalToGlobal.CharacterGerms.ContentZeroAt
public import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective

@[expose] public section

open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oddLevelBlock_bound_attained : BiSupply ∧ RF.BiSupply := by
  first | exact @GlobalTheory.oddBlock_supply | exact GlobalTheory.oddBlock_supply | (intros; apply GlobalTheory.oddBlock_supply <;> assumption)
