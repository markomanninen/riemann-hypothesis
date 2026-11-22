module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataLevel

@[expose] public section

namespace Formalism.BasicNotions

def LevelData (D : D7) :=
  letI := D.host.cmStar
  ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)

end Formalism.BasicNotions
