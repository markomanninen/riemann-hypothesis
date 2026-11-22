module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueHaarDensityAtIdentity
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
public import Formalism.PeriodIntegrals.QuotInv
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.LocalRingCardinality.DataCD

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_haarDensity_at_identity : ∀ (m : ℕ) (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (PI.MtM m)), PI.IsMatGroup S → PI.IsHaarOnM S μ → ∃ c : ℝ, 0 < c ∧ HasDens S μ (ENNReal.ofReal c) ∧ ∀ c', HasDens S μ c' → c' = ENNReal.ofReal c := by
  first | exact @GlobalTheory.MatHaarDensity.exists_hasDens | exact GlobalTheory.MatHaarDensity.exists_hasDens | (intros; apply GlobalTheory.MatHaarDensity.exists_hasDens <;> assumption)
