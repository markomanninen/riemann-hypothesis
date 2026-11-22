module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeTraceDualAndTraceDualTraceDual
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetDetNormPos

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.MeanDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLattice_traceDual_and_traceDual_traceDual : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Submodule.IsFullLattice E Λ → Submodule.IsFullLattice E (trDual E j Λ) ∧ trDual E j (trDual E j Λ) = Λ := by
  exact GlobalTheory.MeanDual.Alg.isLattice_trDual_and_trDual_trDual
