module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBesselCellGapConstant
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
theorem _root_.GlobalTheory.T.exists_besselCell_gap_constant : ∃ Cgf : ℝ, ∀ (D : Formalism.BasicNotions.D7) (ε : Fin (2 * D.R.rS + D.R.k + 1) → Bool) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), Formalism.QuantumDeterminants.GapAtLeast ε lam (Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)) → ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h ∧ GlobalTheory.CellAmp.GapCell D.R.k D.R.rS h := by
  first | exact @GlobalTheory.GapConstant.gap_constant_exists | exact GlobalTheory.GapConstant.gap_constant_exists | (intros; apply GlobalTheory.GapConstant.gap_constant_exists <;> assumption)
