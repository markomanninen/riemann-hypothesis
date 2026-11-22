module

public import Development.EtaleCohomology.CohomologicalPurity.LeafAWCut
public import Development.EtaleCohomology.CohomologicalPurity.LeafAWCutTw

@[expose] public section

theorem LateralTheory.CohomologicalPurity.LeafAWCut.LeafAW_of : LateralTheory.CohomologicalPurity.LeafAW :=
  LateralTheory.CohomologicalPurity.LeafAWCut.goal_of LateralTheory.CohomologicalPurity.LeafAWCutTw.twSec
