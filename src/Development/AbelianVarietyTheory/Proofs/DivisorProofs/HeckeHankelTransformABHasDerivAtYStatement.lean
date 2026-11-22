module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeHankelTransformABHasDerivAtY
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTransABTwoZero

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeHankelTransformAB_hasDerivAt_y : ∀ (a b : ℕ) (σ : ℂ) (ν y : ℝ), 2 ≤ a + b → σ ∈ halfPlane → y ≠ 0 →
    HasDerivAt (fun y' : ℝ => hTransAB a b σ ν y')
      (I * (-(a : ℂ) - σ) * hTransAB (a + 1) b σ ν y + I * ((b : ℂ) + σ) * hTransAB a (b + 1) σ ν y) y := by
  first | exact @GlobalTheory.HeckeTwo.hTransAB_hasDerivAt | exact GlobalTheory.HeckeTwo.hTransAB_hasDerivAt | (intros; apply GlobalTheory.HeckeTwo.hTransAB_hasDerivAt <;> assumption)
