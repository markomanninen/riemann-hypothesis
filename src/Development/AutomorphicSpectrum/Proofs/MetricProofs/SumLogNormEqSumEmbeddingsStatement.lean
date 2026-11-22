module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumLogNormEqSumEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_logNorm_eq_sum_embeddings : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ), IsArithVar p 0 → ∀ (M : HermLB p) (ν : Weight t τ M.B), WOver M.φ ν → ∀ (r : M.B.ι → X.functionFieldˣ), IsRatSec M.B r → ∑ᶠ y : CxPts t τ, logNorm ν r y = ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts p σ, logNorm (M.φ σ) r y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.sum_logNorm_curve | exact GlobalTheory.CompanionTheory.Ar.BaseZ.sum_logNorm_curve | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.sum_logNorm_curve <;> assumption)
