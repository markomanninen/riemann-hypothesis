module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LValEtaBounds
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lValEta_mem_Icc_two_pow_fDeg : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ i : ℕ, 2 ≤ i → ((2 : ℝ) ^ (Formalism.HermitianLatticesTheory.fDeg K))⁻¹ ≤ Formalism.HermitianLatticesTheory.lValEta K i ∧ Formalism.HermitianLatticesTheory.lValEta K i ≤ 2 ^ (Formalism.HermitianLatticesTheory.fDeg K) := by
  first | exact @GlobalTheory.EtaValueBound.lValEta_bounds | exact GlobalTheory.EtaValueBound.lValEta_bounds | (intros; apply GlobalTheory.EtaValueBound.lValEta_bounds <;> assumption)
