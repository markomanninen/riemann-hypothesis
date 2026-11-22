module

public import Development.EtaleCohomology.CohomologicalPurity.LeafAWCutFin

@[expose] public section

namespace LateralTheory.Fin.LeafAW
theorem etale_purity_aw : LateralTheory.CohomologicalPurity.LeafAW := by
  apply LateralTheory.CohomologicalPurity.LeafAWCut.LeafAW_of
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafAW := etale_purity_aw
end LateralTheory.Fin.LeafAW
