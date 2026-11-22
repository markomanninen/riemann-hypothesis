module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinsetIntegralScaledBoxPiCosetReps
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatConvolutionLocalFieldPower

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_integralScaledBoxPi_coset_reps : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (r R : kˣ), valuation k (r : k) ≤ valuation k (R : k) → ∃ S : Finset (n → k), (∀ b ∈ S, b ∈ box n R) ∧ ∀ a ∈ box n R, ∃! b, b ∈ S ∧ a - b ∈ box n r := by
  first | exact @GlobalTheory.BoxReps.exists_finset_box_reps | exact GlobalTheory.BoxReps.exists_finset_box_reps | (intros; apply GlobalTheory.BoxReps.exists_finset_box_reps <;> assumption)
