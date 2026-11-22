module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMapMultipleIsometryLargeGap
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
public import Formalism.LocalRingCardinality.DataTies

@[expose] public section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselMap_multipleIsometry_largeGap : GlobalTheory.GapIn.Hyp → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), 1000 ≤ Cl → (∀ τ w w' θ (W : LocW D.R.k D.R.rS), GoodW D τ w w' θ W → 0 < θ) → (∀ w, 0 < Tr D w) → BSch D large₂ C' Cl Cg cb Cu cT CT C0 := by
  first | exact @GlobalTheory.BesselSchurGap.bessel_schur | exact GlobalTheory.BesselSchurGap.bessel_schur | (intros; apply GlobalTheory.BesselSchurGap.bessel_schur <;> assumption)
