module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardIsometriesFixingSubspaceDefiniteLatticesLe
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_isometries_fixing_subspace_definite_lattices_le : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (U : Submodule K V) (L L' : Submodule (𝓞 K) V), Submodule.IsFullLattice K L → Submodule.IsFullLattice K L' → ((({η : V ≃ₗ[K] V | η ∈ isomGrp H ∧ imLat η L = L' ∧ ∀ y ∈ U, η y = y}).encard : ℕ∞) : ℝ≥0∞) ≤ ((4 * ((Module.finrank K V) - Module.finrank K U) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ≥0∞) ^ (4 * ((Module.finrank K V) - Module.finrank K U) * (Formalism.HermitianLatticesTheory.fDeg K)) := by
  first | exact @GlobalTheory.IsoCount.isoCnt | exact GlobalTheory.IsoCount.isoCnt | (intros; apply GlobalTheory.IsoCount.isoCnt <;> first | assumption | exact (by assumption : Submodule.IsFullLattice _ _).toIsLattice)
