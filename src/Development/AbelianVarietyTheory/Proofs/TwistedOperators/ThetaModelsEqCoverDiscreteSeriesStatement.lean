module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsEqCoverDiscreteSeries
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BarMatrix
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaModels_eq_coverDiscreteSeries : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D := by
  first | exact @GlobalTheory.modelsAreCoverSeries_of_hypotheses | exact GlobalTheory.modelsAreCoverSeries_of_hypotheses | (intros; apply GlobalTheory.modelsAreCoverSeries_of_hypotheses <;> assumption)
