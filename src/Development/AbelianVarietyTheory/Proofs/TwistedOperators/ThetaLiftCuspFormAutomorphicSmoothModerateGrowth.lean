module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspRapidDecayOfSobolev
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelModerateGrowthWithSeminormsStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RapidDecayLift
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum

namespace GlobalTheory.Chain.LiftReg

theorem liftProps_obj : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.LiftProps D :=
  fun hP D => liftProps_of_rapidDecay hP D (GlobalTheory.T.thetaKernel_moderateGrowth_with_seminorms D)

end GlobalTheory.Chain.LiftReg
