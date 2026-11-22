module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSupportSplitCentreFactor
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousResQ
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicGLNormOneSplitStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureNormOneProductStatement

@[expose] public section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_support_split_centre_factor : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ν : Measure (normOneGL (K := E) (n := a))) [ν.IsHaarMeasure] (c : ENNReal), c ≠ 0 → c ≠ ⊤ → Measure.map (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ → ∀ f : GA E a → ℂ, Continuous f → HasCompactSupport f → ∃ f₁ : CompactlySupportedContinuousMap (normOneGL (K := E) (n := a)) ℂ, ∀ (K : Type) [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K] (W : GA E a → K), Continuous W → (∀ t g, W (splitCentre E a t * g) = W g) → ∫ g, f g • W g ∂μ = ∫ x, f₁ x • W (x : GA E a) ∂ν := by
  first | exact @GlobalTheory.CompanionTheory.CuspTransfer.FubiniCentre.exists_normOne_integral | exact GlobalTheory.CompanionTheory.CuspTransfer.FubiniCentre.exists_normOne_integral | (intros; apply GlobalTheory.CompanionTheory.CuspTransfer.FubiniCentre.exists_normOne_integral <;> assumption)
