module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsQuotientMeasureWeil
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.PeriodIntegrals.QuotSetU
public import Formalism.PeriodIntegrals.QuotInv

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotientMeasure_weil : ∀ (m : ℕ) (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μG μS : Measure (PI.MtM m)), PI.IsMatGroup G → PI.IsMatGroup S → S ⊆ G → PI.IsHaarOnM G μG → PI.IsHaarOnM S μS → PI.IsRightInvM S μS → ∃ ν, PI.IsQuotM μG μS ν := by
  first | exact @GlobalTheory.QuotWeil.exists_isQuotM | exact GlobalTheory.QuotWeil.exists_isQuotM | (intros; apply GlobalTheory.QuotWeil.exists_isQuotM <;> assumption)
