module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LastMajorantLengthSqGeAndPos
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
public import Formalism.LocalRingCardinality.DataTies

@[expose] public section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_majorant_length_sq_ge_and_pos : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z → ∀ g ∈ GG k r, Tz k r z ≤ lenA k r z g (Fin.last r) ^ 2 ∧ ∀ a, 0 < lenA k r z g a ∧ lenA k r z g a = lA k r z g a := by
  first | exact @GlobalTheory.LastLen.last_len | exact GlobalTheory.LastLen.last_len | (intros; apply GlobalTheory.LastLen.last_len <;> assumption)
