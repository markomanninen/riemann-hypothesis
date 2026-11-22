module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesHarishChandraModuleAdmissible

@[expose] public section

open Formalism.BasicNotions

namespace GlobalTheory.TwArch

theorem archOnRecord_closed : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
    ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ArchOnRecord D :=
  fun hDS hHC D => GlobalTheory.ArchRec.archOnRecord hDS hHC D

end GlobalTheory.TwArch
