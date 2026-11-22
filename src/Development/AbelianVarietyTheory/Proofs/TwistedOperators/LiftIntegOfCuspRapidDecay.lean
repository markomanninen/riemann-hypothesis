module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelModerateGrowthWithSeminormsStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.Chain.LiftConv

theorem liftInteg_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, GlobalTheory.Chain.LiftInteg D :=
  fun hP D => liftInteg_of_growth hP D (GlobalTheory.T.thetaKernel_moderateGrowth_with_seminorms D)

end GlobalTheory.Chain.LiftConv
