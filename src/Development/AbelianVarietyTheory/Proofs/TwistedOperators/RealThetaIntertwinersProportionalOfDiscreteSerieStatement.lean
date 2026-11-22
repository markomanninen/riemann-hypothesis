module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinersProportionalOfDiscreteSerie
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realThetaIntertwiners_proportional_of_discreteSeries : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.Chain.ItLine D := by
  first | exact @GlobalTheory.Chain.RealLine.itLine_of_discreteSeries | exact GlobalTheory.Chain.RealLine.itLine_of_discreteSeries | (intros; apply GlobalTheory.Chain.RealLine.itLine_of_discreteSeries <;> assumption)
