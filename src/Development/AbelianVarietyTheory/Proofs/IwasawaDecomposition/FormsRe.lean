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
def formsRe {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (T : FormsTiedSym D u Ch chOf) :
    FormsTiedSym (reD D Z) u Ch chOf :=
  { T with
    atT := { T.atT with }
    cls := fun i hi h => { T.cls i hi h with }
    val := fun i hi h => { T.val i hi h with }
    lv := fun i hi => { T.lv i hi with }
    ch := fun i h1 h2 β => { T.ch i h1 h2 β with }
    valC := fun i h1 h2 => { T.valC i h1 h2 with }
    dilC := fun i h1 h2 => { T.dilC i h1 h2 with }
    lvC := fun i h1 h2 => { T.lvC i h1 h2 with }
    clsP := { T.clsP with }
    valP := { T.valP with }
    til := { T.til with }
    tilAd := { T.tilAd with } }

end GlobalTheory.Mem.SRe.ColRe

end
