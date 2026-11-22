module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBesselMapsLargeGapPeriodIdentities
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
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
theorem _root_.GlobalTheory.T.exists_besselMaps_largeGap_periodIdentities : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ), Formalism.QuantumDeterminants.GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.c ≠ 0 → 0 < L.κN → L.κN ≠ ⊤ → ∃ (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq), GlobalTheory.AmpTK.BeTK L l l' ∧ GlobalTheory.AmpTK.SmCW L l ∧ GlobalTheory.AmpTK.SmCW L l' := by
  first | exact @GlobalTheory.AmpTKGap.exists_besselTK | exact GlobalTheory.AmpTKGap.exists_besselTK | (intros; apply GlobalTheory.AmpTKGap.exists_besselTK <;> assumption)
