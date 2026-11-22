module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockHarmonicRepresentative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerDecompositionFockNoncompactParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumLineMatrixKroneckerRightFactor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStable

@[expose] public section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fockHarmonic_representative : ∀ (P Q R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (pr : Pol P Q R S →ₗ[ℂ] W), (∀ Z : Mat P Q, IsPC Z → ∀ f, pr (fockAct1 P Q R S Z f) = 0) → ∀ f, ∃ h ∈ harm2 P Q R S, pr h = pr f := by
  first | exact @GlobalTheory.FockAlg.HarmLift.exists_harm2_rep | exact GlobalTheory.FockAlg.HarmLift.exists_harm2_rep | (intros; apply GlobalTheory.FockAlg.HarmLift.exists_harm2_rep <;> assumption)
