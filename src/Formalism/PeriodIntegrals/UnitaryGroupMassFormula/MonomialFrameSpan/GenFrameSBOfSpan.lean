module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.GenFrameSBOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.StepBack
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.SatFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.SatProj

@[expose] public section

namespace GenFrameSpan

theorem stepSat : StepSat := stepSat_of projZ

theorem genFrameSB_of_span (hs : StepSpan) : CutKW.KWsb := genFrameSB_of stepBack hs stepSat

end GenFrameSpan
