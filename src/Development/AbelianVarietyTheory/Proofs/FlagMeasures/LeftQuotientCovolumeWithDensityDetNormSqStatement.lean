module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeWithDensityDetNormSq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leftQuotientCovolume_withDensity_detNormSq : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (j : ℕ), 1 ≤ j → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsFullLattice E Λ → ∀ F : ℝ → ENNReal, Measurable F → covol (autGL E j Λ) ((haarGL E j).withDensity fun x => F (detNorm E j x)) {x | 0 < detNorm E j x} = covol (autGL E j Λ) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} * ∫⁻ t in Set.Ioi (0 : ℝ), F t / ENNReal.ofReal t := by
  intro E _ _ hE j hj Λ hΛ F hF
  first
  | exact GlobalTheory.DetSlab.covol_withDensity_detNorm E hE j hj Λ hΛ F hF
  | exact GlobalTheory.DetSlab.covol_withDensity_detNorm E hE j hj Λ hΛ.toIsLattice F hF
