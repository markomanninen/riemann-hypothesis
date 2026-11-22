module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureRightInvariant
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.PeriodIntegrals.QuotSetU
public import Formalism.PeriodIntegrals.QuotInv

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientMeasure_right_invariant : PI.QuotInv := by
  first | exact @GlobalTheory.QuotRightInv.quotInv | exact GlobalTheory.QuotRightInv.quotInv | (intros; apply GlobalTheory.QuotRightInv.quotInv <;> assumption)
