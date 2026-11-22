module

public import Formalism.MahlerMeasure.MahlerMeasureProofs.LevelSum
public import Formalism.MahlerMeasure.MahlerMeasureProofs.LevelAct
public import Formalism.MahlerMeasure.MahlerMeasureProofs.FreezeInto
public import Formalism.MahlerMeasure.MahlerMeasureProofs.FreezeBij
public import Formalism.MahlerMeasure.MahlerMeasureProofs.FreezeY
public import Formalism.MahlerMeasure.MahlerMeasureProofs.LevelDecomp
public import Formalism.MahlerMeasure.MahlerMeasureProofs.PhiInt
public import Formalism.MahlerMeasure.MahlerMeasureProofs.RemoveS
public import Formalism.MahlerMeasure.QuotientUpperBoundsOfPowerBounds

@[expose] public section

namespace Formalism.GM.Top
open Formalism.GM
theorem levelAct : LevelAct := levelAct_of alternatingChooseSum
end Formalism.GM.Top
