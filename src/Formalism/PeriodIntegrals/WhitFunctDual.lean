module

public import Mathlib
public import Formalism.PadicSubsetSums.CentralIdempotents.EigenbasisOfDistinctRoots
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolicBase

@[expose] public section

namespace PI

def WhitFunctDual : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.GelfandGraevMultOne → Formalism.L2.SG.GGMirabolic.GelfandGraevMultOne

end PI
