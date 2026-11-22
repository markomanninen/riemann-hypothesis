module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RedivisionStructureEq
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Lean

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.SRe.ColRe

open Formalism.BasicNotions Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.SRe NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)


set_option maxHeartbeats 4000000 in
def hermRe (H : Formalism.L2.Herm.ColsHermS D) : Formalism.L2.Herm.ColsHermS (reD D Z) :=
  { H with
    base := { H.base with }
    atT := fun u => { H.atT u with }
    ad := { H.ad with } }

end GlobalTheory.Mem.SRe.ColRe

end
