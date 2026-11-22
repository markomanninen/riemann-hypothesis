module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuesWithModerateGrowthShiftTranslatePow
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
public import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero

@[expose] public section

open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuesWithModerateGrowth_shift_translate_pow : ∀ (D : D7) (T : HSp D) (e e' : ℂ → GA D T → ℂ) (x : GA D T) (c : ℝ≥0) (s₁ s₂ : ℂ), 0 < c → (∀ s g, e' s g = npow c (s₁ - s) * e (s + s₂) (g * x)) → ContMod T e → ContMod T e' := by
  first | exact @GlobalTheory.EisCont.Shift.contMod_shift | exact GlobalTheory.EisCont.Shift.contMod_shift | (intros; apply GlobalTheory.EisCont.Shift.contMod_shift <;> assumption)
