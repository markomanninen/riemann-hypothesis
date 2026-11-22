module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDensityAtIdentityUnitaryGroupProbability
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
public import Formalism.PeriodIntegrals.QuotInv
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.LocalRingCardinality.DataCD

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDensityAtIdentity_unitaryGroup_probability : ∀ (j : ℕ) (μ : Measure (PI.MtM j)), PI.IsHaarOnM (UH (1 : Matrix (Fin j) (Fin j) ℂ)) μ → μ Set.univ = 1 → HasDens (UH (1 : Matrix (Fin j) (Fin j) ℂ)) μ (ENNReal.ofReal (volUn j)⁻¹) := by
  first | exact @GlobalTheory.UnitaryVolume.hasDens_unitary | exact GlobalTheory.UnitaryVolume.hasDens_unitary | (intros; apply GlobalTheory.UnitaryVolume.hasDens_unitary <;> assumption)
