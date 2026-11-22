module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylModuleSimpleClosedLowestAlcove
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylModule_simple_closedLowestAlcove : GlobalTheory.Published.InducedSimpleLowestAlcove := by
  first | exact @GlobalTheory.Alc.inducedSimpleLowestAlcove | exact GlobalTheory.Alc.inducedSimpleLowestAlcove | (intros; apply GlobalTheory.Alc.inducedSimpleLowestAlcove <;> assumption)
