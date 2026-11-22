module

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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBesselCellGapConstantStatement
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselCoefficientNonzero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellTrivialStabiliserAndMeasuresStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairSpaceMajorantIntegrableBigCellStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallCellRelevantPointsHaarQuotientMajorantStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPeriodPositivity
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselCoefficientNonzeroExists

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.AmpTK

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

theorem kfin_zero {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) :
    Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) σ 0 :=
  ⟨⊥, inferInstance, Submodule.zero_mem _, fun g _ x hx => by
    rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero]⟩

theorem isCoef_zero {k r : ℕ} (L : LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) :
    IsCoef (rep L) l l' (fun _ => 0) 0 :=
  ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun g _ => by simp, by simp⟩

end GlobalTheory.AmpTK
