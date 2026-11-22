module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNarrowRayClassLFunctionTopWideIndicatorIff
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateWideInd

@[expose] public section

open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNarrowRayClassLFunction_top_wideIndicator_iff : ∀ {F : Type} [Field F] [NumberField F] (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ), IsRayL (⊤ : Ideal (𝓞 F)) (wideInd C) Z ↔ IsClassZeta C Z := by
  first | exact @GlobalTheory.ZetaDenom.isRayL_top_wideInd_iff | exact GlobalTheory.ZetaDenom.isRayL_top_wideInd_iff | (intros; apply GlobalTheory.ZetaDenom.isRayL_top_wideInd_iff <;> assumption)
