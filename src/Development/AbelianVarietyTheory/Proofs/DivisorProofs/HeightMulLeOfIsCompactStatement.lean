module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightMulLeOfIsCompact
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_height_mul_le_of_isCompact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∃ B : ℝ, 1 ≤ B ∧ ∀ c ∈ Ω, ∀ y : GL (Fin a) (Cinf E), height (y * c) ≤ B * height y := by
  first | exact @GlobalTheory.AutGrowth.height_mul_le_of_isCompact | exact GlobalTheory.AutGrowth.height_mul_le_of_isCompact | (intros; apply GlobalTheory.AutGrowth.height_mul_le_of_isCompact <;> assumption)
