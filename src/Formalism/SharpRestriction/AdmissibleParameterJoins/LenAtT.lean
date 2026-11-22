module

public import Formalism.LocalRingCardinality.Lemmas
public import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLd

@[expose] public section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

theorem lenAtT (D : D7) (L : SizeData₂ D) (hAtT : NuAtTDef D L) : LenAtT D L :=
  fun u w hw => D.lenLoc_atT hAtT u w hw

theorem locSpan (D : D7) : LocSpan D := fun u w y hy => D.locSpan u w y hy

end Formalism.MainNotions.J
