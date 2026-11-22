module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralCompAddEquivRescale
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGaussIntegral_comp_addEquiv_rescale : ∀ (X Y : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (μ : Measure X) (μ' : Measure Y) (T : X ≃ₜ+ Y) (r : NNReal) (f : Y → ℂ) (γ : ℂ), μ.map T = r • μ' → HasGauss μ' f γ → HasGauss μ (fun x => f (T x)) ((r : ℝ) * γ) := by
  first | exact @GlobalTheory.KSp.hasGauss_comp_equiv | exact GlobalTheory.KSp.hasGauss_comp_equiv | (intros; apply GlobalTheory.KSp.hasGauss_comp_equiv <;> assumption)
