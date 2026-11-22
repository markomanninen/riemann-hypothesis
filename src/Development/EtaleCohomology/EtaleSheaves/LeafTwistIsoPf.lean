module

public import Development.EtaleCohomology.EtaleSheaves.LeafKillCut
public import Development.EtaleCohomology.EtaleSheaves.LeafTwInjPf
public import Development.EtaleCohomology.EtaleSheaves.LeafTwSurjPf
public import Development.EtaleCohomology.EtaleSheaves.PullMonoPf
public import Development.EtaleCohomology.EtaleSheaves.LocSecPfC
public import Development.EtaleCohomology.EtaleSheaves.ClassSecPf

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTwistIsoPf

theorem leafLoc : LateralTheory.E.LeafTwistPf.LeafLoc :=
  LateralTheory.E.LeafLocPf.LeafLoc_of' (LateralTheory.E.LocSecPfC.LocSec_of LateralTheory.E.ClassSecPf.ClassSec_of)
    (LateralTheory.E.LocSlicePf.LocSlice_of' LateralTheory.E.PullMonoPf.PullMono_of)

theorem leafTwSec : LateralTheory.E.LeafTwistPf.LeafTwSec :=
  LateralTheory.E.LeafTwSecPf.LeafTwSec_of' LateralTheory.E.LeafTwInjPf.LeafTwInj_of LateralTheory.E.LeafTwSecPf.LeafTwSurj_of

end LateralTheory.E.LeafTwistIsoPf

end
