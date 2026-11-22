module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftCuspFormAutomorphicSmoothModerateGrowth
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RapidDecayLift
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_cuspForm_automorphic_smooth_moderateGrowth : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.LiftProps D := by
  first | exact @GlobalTheory.Chain.LiftReg.liftProps_obj | exact GlobalTheory.Chain.LiftReg.liftProps_obj | (intros; apply GlobalTheory.Chain.LiftReg.liftProps_obj <;> assumption)
