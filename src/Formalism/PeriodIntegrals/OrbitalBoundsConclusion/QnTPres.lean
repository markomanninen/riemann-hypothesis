module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinorSmoothness.SecondCapelliMinorContinuousLinear
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnTInv

@[expose] public section

theorem qnTPres : Formalism.FourierDecayAlt.Q.TPreservesFF := Formalism.FourierDecayAlt.Q.TPresMain.qnTPres_of qnTInv
