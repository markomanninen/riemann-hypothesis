module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedTranslateClassInvariantOfMemThetaSpace
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PderivIterEqPderivListOfDifferentiableOn
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedTranslateClassInvariant_of_mem_thetaSpace : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ : AddSubgroup (VC D N N')) (F : VC D N N' → ℂ), (∀ x ∈ A₂, ∃ m : ℤ, qH D T x = m) → (∀ x ∈ A₂, ∀ y ∈ A₂, ∃ m : ℤ, (Hf D T (w0 D • x) y).im = m) → F ∈ ThSp D T A₁ → RepInd D T A₁ A₂ F := by
  first | exact @GlobalTheory.ThetaConj.repInd_of_thSp | exact GlobalTheory.ThetaConj.repInd_of_thSp | (intros; apply GlobalTheory.ThetaConj.repInd_of_thSp <;> assumption)
