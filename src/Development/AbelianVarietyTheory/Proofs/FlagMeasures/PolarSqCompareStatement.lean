module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PolarSqCompare
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
theorem _root_.GlobalTheory.T.polar_tanSq_ptSq_compare : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ), 1 < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ u : ℝ × Sp P' Q', u.1 ∈ Set.Ioo (-Real.pi) Real.pi → (tanSq u < (t⁻¹ * r) ^ 2 → ptSq e (polarPt e u) < r ^ 2) ∧ (ptSq e (polarPt e u) < r ^ 2 → tanSq u < (t * r) ^ 2) := by
  first | exact @GlobalTheory.PolarCompare.polar_sq_compare | exact GlobalTheory.PolarCompare.polar_sq_compare | (intros; apply GlobalTheory.PolarCompare.polar_sq_compare <;> assumption)
