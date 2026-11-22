module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GkMapCuspFormsExtendsToSmoothVectors
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gkMapCuspForms_extends_to_smoothVectors : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.GKExtension D := by
  first | exact @GlobalTheory.GKExtensionToSmoothVectors.gkExtension | exact GlobalTheory.GKExtensionToSmoothVectors.gkExtension | (intros; apply GlobalTheory.GKExtensionToSmoothVectors.gkExtension <;> assumption)
