module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHermitianNormFibreDilation
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousGaussSp

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_hermitianNormFibre_dilation : ∀ (P Q : ℕ) (fib : ℝ → Measure (Sp P Q)) (β t : ℝ), IsDxDq fib → β ≠ 0 → 0 < t → ∀ φ : Sp P Q → ℝ≥0∞, Measurable φ → ∫⁻ y, φ y ∂(fib (t * β)) = ENNReal.ofReal (t ^ (P + Q) / t) * ∫⁻ y, φ (Real.sqrt t • y) ∂(fib β) := by
  first | exact @GlobalTheory.FibreScaling.lintegral_fibre_scale | exact GlobalTheory.FibreScaling.lintegral_fibre_scale | (intros; apply GlobalTheory.FibreScaling.lintegral_fibre_scale <;> assumption)
