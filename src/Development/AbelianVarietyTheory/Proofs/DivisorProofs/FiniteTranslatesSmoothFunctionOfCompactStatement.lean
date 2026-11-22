module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTranslatesSmoothFunctionOfCompact
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_translates_smoothFunction_of_compact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsOpen {k | finRep E a k φ = φ} → ∀ Kf : Set (GL (Fin a) (Af E)), IsCompact Kf → ∃ S : Finset (GL (Fin a) (Af E)), ∀ f ∈ Kf, ∃ f' ∈ S, finRep E a f φ = finRep E a f' φ := by
  first | exact @GlobalTheory.finite_translates_of_isCompact | exact GlobalTheory.finite_translates_of_isCompact | (intros; apply GlobalTheory.finite_translates_of_isCompact <;> assumption)
