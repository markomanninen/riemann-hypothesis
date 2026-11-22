module

public import Formalism.MahlerMeasure.FinalM
public import Formalism.MahlerMeasure.MahlerMeasureProofs.GamDeg
public import Formalism.MahlerMeasure.MahlerMeasureProofs.GamLead
public import Formalism.MahlerMeasure.MahlerMeasureProofs.GamInt

@[expose] public section

namespace Formalism.GM.Top
open Formalism.GM
theorem gamDeg : M.GamDeg := gamma_degree_bound
theorem gamLead : M.GamLead := gamma_leading_term
end Formalism.GM.Top
