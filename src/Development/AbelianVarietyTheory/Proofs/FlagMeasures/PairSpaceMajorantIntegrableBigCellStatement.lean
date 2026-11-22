module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairSpaceMajorantIntegrableBigCell
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPtRepTrDat
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
public import Formalism.LocalRingCardinality.DataTies
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.JEqOrbInt

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_space_majorant_integrable_big_cell : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ), Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GlobalTheory.CellAmp.GapCell k r h → L.κN ≠ ⊤ → 0 < L.κN → L.c ≠ 0 → ∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) → μᴴ * Formalism.QuantumDeterminants.Hb k * μ = Formalism.QuantumDeterminants.Hb k → ∃ b : ℝ, 0 ≤ b ∧ Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b ∧ MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj (Formalism.QuantumDeterminants.bigCell k r c μ) b) (Formalism.MainNotions.S.pairMeas L) := by
  first | exact @GlobalTheory.BigConv.bigConv | exact GlobalTheory.BigConv.bigConv | (intros; apply GlobalTheory.BigConv.bigConv <;> assumption)
