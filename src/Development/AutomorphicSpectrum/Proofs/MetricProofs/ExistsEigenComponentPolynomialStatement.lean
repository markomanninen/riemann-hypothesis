module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsEigenComponentPolynomial
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositiveStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigenComponent_polynomial : ∀ (E : Type) [Field E] [NumberField E] (s₀ : 𝓞 E →+* ℂ), ∃ c : 𝓞 E →₀ ℂ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : 𝓞 E →+* Module.End ℂ V), (∀ x, eigComp ρ s₀ x = ∑ a ∈ c.support, c a • ρ a x) ∧ (∀ x, eigComp ρ s₀ x ∈ eigSp ρ s₀) ∧ ∀ x ∈ eigSp ρ s₀, eigComp ρ s₀ x = x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.EigCoef.eigComp_eq_combination | exact GlobalTheory.CompanionTheory.Ar.Cusp.EigCoef.eigComp_eq_combination | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.EigCoef.eigComp_eq_combination <;> assumption)
