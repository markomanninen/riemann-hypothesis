module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeHankelTransformABDifferentiableOnSigma
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTransABTwoZero

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeHankelTransformAB_differentiableOn_sigma : ∀ (a b : ℕ) (ν y : ℝ), 2 ≤ a + b → y ≠ 0 → DifferentiableOn ℂ (fun σ => hTransAB a b σ ν y) halfPlane := by
  first | exact @GlobalTheory.HeckeTwo.hTransAB_differentiableOn | exact GlobalTheory.HeckeTwo.hTransAB_differentiableOn | (intros; apply GlobalTheory.HeckeTwo.hTransAB_differentiableOn <;> assumption)
