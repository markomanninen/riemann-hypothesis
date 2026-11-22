module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSmoothedEisensteinFxWeightOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
public import Development.AbelianVarietyTheory.Definitions.Foundations.CthFac
public import Development.AbelianVarietyTheory.Definitions.Foundations.MultipliableAndSgNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelLinearOperations

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasQExpansion_smoothedEisensteinFx_weightOne : ∀ (c M : ℕ) (a b : ℤ), 0 < M → GlobalTheory.QFam.HasQ M (GlobalTheory.Sieg.cF c 1 ![(a : ℚ) / M, (b : ℚ) / M]) (GlobalTheory.KummerEisensteinGalois.smF (c : ℤ) 1 M (GlobalTheory.Sieg.ee (1 / (M : ℂ))) a b) := by
  first | exact @GlobalTheory.Sieg.EisQ.hasQ_cF_one | exact GlobalTheory.Sieg.EisQ.hasQ_cF_one | (intros; apply GlobalTheory.Sieg.EisQ.hasQ_cF_one; all_goals assumption)
