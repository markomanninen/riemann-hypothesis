module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkewAnalyticGroup.SkewReductionGroup
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkewAnalyticGroup.Analytic

@[expose] public section

theorem qnRdSkew : Formalism.FourierDecayAlt.Q.RdSkew :=
  QnRdSkewW.rdSkew_of QnRdSkewW.skew_reduction_group QnRdSkewW.skew_reduction_analytic
