module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterBlocksAttainBound
public import Formalism.LocalToGlobal.CharacterGerms.ContentLargeFromSupplies
public import Formalism.LocalToGlobal.CharacterGerms.ContentZeroAt

@[expose] public section

open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterBlocks_attain_bound : CHSupply ∧ RF.CHSupply := by
  first | exact @GlobalTheory.CharBlock.chSupply | exact GlobalTheory.CharBlock.chSupply | (intros; apply GlobalTheory.CharBlock.chSupply <;> assumption)
