module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBorelSectionUnitaryOrbitQuadric
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding

@[expose] public section

open MeasureTheory Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_borelSection_unitary_orbit_quadric : ∀ (P Q : ℕ) (β : ℝ) (x₀ : GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q), β ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf x₀ = β → ∃ s : GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q → UpqT P Q, GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.IsSection β x₀ s := by
  first | exact @GlobalTheory.QuadricSection.exists_isSection | exact GlobalTheory.QuadricSection.exists_isSection | (intros; apply GlobalTheory.QuadricSection.exists_isSection <;> assumption)
