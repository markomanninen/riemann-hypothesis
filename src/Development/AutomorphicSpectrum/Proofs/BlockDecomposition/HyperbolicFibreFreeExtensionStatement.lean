module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicFibreFreeExtension
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCell
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StagedDisintegrationCompositionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartGramFirstEntryStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIntegralFormulaHyperbolicStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockDecompositionHomeomorphStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartCompactSupportContinuousStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCellOpenIndependentStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousDensitiesEqOfIntegralsOnCompactsStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicSumNondegenerateFrame
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorelStatement

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_fibre_free_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (hypOne J) (n + 1) (coordW R b lam (n + 1) (M + 2)) (coordHerm R σ b lam (n + 1)) m → IsGramFibFree R σ (hypOne J) 1 (coordW R b lam 1 (M + 2)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ freeCell (R ⊗[F] E) M n → (∀ X, 0 ≤ φ X) → ∫⁻ X, ENNReal.ofReal (φ X) ∂(m 0) = ∫⁻ x, ∫⁻ a, ∫⁻ Y, ENNReal.ofReal (φ (chartS R σ J x a 0 Y)) ∂(m' 0) ∂(coordW R b lam 1 n) ∂(m₁ 0) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StagesZero.stages_zero | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StagesZero.stages_zero | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StagesZero.stages_zero <;> assumption)
