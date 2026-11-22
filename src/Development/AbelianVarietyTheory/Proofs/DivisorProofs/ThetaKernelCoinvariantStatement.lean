module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelCoinvariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kernel_coinvariant : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.KCoinv := by
  first | exact @GlobalTheory.KCoinvGood.kCoinv | exact GlobalTheory.KCoinvGood.kCoinv | (intros; apply GlobalTheory.KCoinvGood.kCoinv <;> assumption)
