module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCutoffOfAddCharTranslationInvariantFunctio
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatConvolutionLocalFieldPower
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralScaledBoxPiSupersetOfIsCompactStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinsetIntegralScaledBoxPiCosetRepsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumIntegralScaledBoxPiCosetRepsShiftInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralBoxInvariantEqMeasureRealMulSumRepsStatement

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cutoff_of_addChar_translation_invariant_functional : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (b : I₁ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) → l Φ' = l Φ) → ∀ (Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))) (s : kˣ), ∃ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), (∀ x, Φ'.1 x = (box I₁ s).indicator (fun _ => (1 : ℂ)) x.2.1 * Φ.1 x) ∧ l Φ = l Φ' := by
  first | exact @GlobalTheory.CharCutoff.exists_cutoff_of_char_invariant | exact GlobalTheory.CharCutoff.exists_cutoff_of_char_invariant | (intros; apply GlobalTheory.CharCutoff.exists_cutoff_of_char_invariant <;> assumption)
