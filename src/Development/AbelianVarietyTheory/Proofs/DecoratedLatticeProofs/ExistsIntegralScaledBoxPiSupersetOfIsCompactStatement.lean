module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralScaledBoxPiSupersetOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatConvolutionLocalFieldPower

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralScaledBoxPi_superset_of_isCompact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (K : Set (n → k)), IsCompact K → ∀ r : kˣ, ∃ R : kˣ, valuation k (r : k) ≤ valuation k (R : k) ∧ K ⊆ box n R := by
  first | exact @GlobalTheory.exists_box_superset_of_isCompact | exact GlobalTheory.exists_box_superset_of_isCompact | (intros; apply GlobalTheory.exists_box_superset_of_isCompact <;> assumption)
