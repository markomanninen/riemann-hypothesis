module

public import Development.EtaleCohomology.EtaleSheaves.EmptySec
public import Development.EtaleCohomology.EtaleSheaves.DerivUnit
public import Development.EtaleCohomology.EtaleSheaves.HensQuot

@[expose] public section

namespace LateralTheory.E.LeafClosedSH0PfCut
open LateralTheory.E.LeafClosedSH0Pf

theorem LeafClosedSH0_of (hS : LeafSHSieve) : LateralTheory.E.LeafVanBPf.LeafClosedSH0 :=
  LateralTheory.E.LeafClosedSH0Pf.LeafClosedSH0_of hS LateralTheory.E.LeafClosedSH0PfQuot.shQuot
    LateralTheory.E.LeafClosedSH0PfEmpty.emptySec LateralTheory.E.LeafClosedSH0PfPrim.primLift

end LateralTheory.E.LeafClosedSH0PfCut
