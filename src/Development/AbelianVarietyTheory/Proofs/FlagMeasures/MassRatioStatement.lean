module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMassRatioUnimodularDefiniteStatement

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.MassAtRecord

theorem massRatio_at_record : ∀ D : D7, UnitaryVolumeMass.stMassRatio D := fun D => by
  letI := D.host.cmStar
  exact fun j hj V V' _ _ _ _ _ _ _ _ f f' L L' hs hs' ho ho' =>
    GlobalTheory.T.siegel_massRatio_unimodular_definite D.host.E D.sp.cm.cmUnram j hj V V' f f' L L' hs hs' ho ho'

end GlobalTheory.MassAtRecord
