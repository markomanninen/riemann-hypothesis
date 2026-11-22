module

public import Mathlib
public import Formalism.UnipotentAdelicQuotients.SiegelSetsSL2Adelic
public import GroundTheory.IdeleRoots.ClassicalIdeles.ExistsPosBoundsOfIsCompact

@[expose] public section

namespace GlobalTheory.CompanionTheory.Classical

theorem siegelSetsSL2Adelic_tie : Formalism.D.siegelSetsSL2Adelic :=
  GroundTheory.BlockD.siegelSetsSL2Adelic_holds

end GlobalTheory.CompanionTheory.Classical
