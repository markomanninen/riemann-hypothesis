module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabiliserSelfDualLatticeLevelIndexFormula
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualLatticeIndex

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabiliser_self_dual_lattice_level_index_formula : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeIndex.StabiliserLevelIndexFormula := by
  first | exact @GlobalTheory.LevelIndex.selfDualLatticeIndex_stabiliserLevelIndexFormula | exact GlobalTheory.LevelIndex.selfDualLatticeIndex_stabiliserLevelIndexFormula | (intros; apply GlobalTheory.LevelIndex.selfDualLatticeIndex_stabiliserLevelIndexFormula <;> assumption)
