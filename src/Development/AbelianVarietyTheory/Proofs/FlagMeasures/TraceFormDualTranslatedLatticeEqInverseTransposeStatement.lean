module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceFormDualTranslatedLatticeEqInverseTranspose
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetDetNormPos

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.MeanDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceFormDual_translatedLattice_eq_inverseTranspose : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Submodule.IsFullLattice E Λ → ∀ g : MatInf E j, 0 < detNorm E j g → dualAt E j (latAt E j Λ g) = latAt E j (trDual E j Λ) (invT E j g) := by
  first | exact @GlobalTheory.MeanDual.dualAt_latAt_eq_latAt_trDual | exact GlobalTheory.MeanDual.dualAt_latAt_eq_latAt_trDual | (intros; apply GlobalTheory.MeanDual.dualAt_latAt_eq_latAt_trDual <;> first | assumption | exact (by assumption : Submodule.IsFullLattice _ _).toIsLattice)
