module

public import Formalism.MahlerMeasure.MahlerMeasureProofs.BadCrit
public import Formalism.MahlerMeasure.MahlerMeasureProofs.MeanGam
public import Formalism.MahlerMeasure.GamLead
public import Formalism.MahlerMeasure.CoarseLevelSlackInequalities

@[expose] public section

namespace Formalism.GM.Top
open Formalism.GM
theorem badCrit : M.BadCrit := bad_criterion_holds
end Formalism.GM.Top
