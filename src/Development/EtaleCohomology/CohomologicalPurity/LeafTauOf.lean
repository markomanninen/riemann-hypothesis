module

public import Development.EtaleCohomology.CohomologicalPurity.LeafTauResPf

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ThomClassRestriction

theorem LeafTau_of (hBd : LeafBd) (hG : LeafGeo) (hPB : LeafPB) (hTl : LeafTail)
    (hU : LeafTauU) (hT : LeafTauTop) : LeafTau :=
  LeafTau_ofU hBd hG hPB hTl hU hT

end LateralTheory.CohomologicalPurity.Thom.ThomClassRestriction
