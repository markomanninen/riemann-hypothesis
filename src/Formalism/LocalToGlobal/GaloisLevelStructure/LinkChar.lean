module

public import Formalism.LocalToGlobal.GaloisLevelStructure.NGalTied
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied

@[expose] public section

namespace Formalism.L2

def NGalTied.TupLink {D : Formalism.BasicNotions.D7} (G : NGalTied D) {C : Host.CharFrame D} {nch : Formalism.BasicNotions.NChoice D}
    (Tp : Host.TupTied D C nch) : Prop :=
  G.tup = Tp.tup

end Formalism.L2
