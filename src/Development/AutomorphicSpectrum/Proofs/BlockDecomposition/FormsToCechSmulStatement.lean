module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormsToCechSmul
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forms_to_cech_smul :
    type_of% @GlobalTheory.CompanionTheory.OmBridge.formToCO_smul :=
  @GlobalTheory.CompanionTheory.OmBridge.formToCO_smul
