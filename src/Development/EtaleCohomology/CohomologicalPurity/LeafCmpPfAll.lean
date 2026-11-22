module

public import Development.EtaleCohomology.CohomologicalPurity.LeafCmpPfNb
public import Development.EtaleCohomology.CohomologicalPurity.LeafCmpPfId

@[expose] public section

namespace LateralTheory.CohomologicalPurity.Cl

theorem LeafCmp_of_Mat (hMat : LeafMat) : LeafCmp := LeafCmp_of hMat LeafCmpNb_pf LeafCmpId_pf

end LateralTheory.CohomologicalPurity.Cl
