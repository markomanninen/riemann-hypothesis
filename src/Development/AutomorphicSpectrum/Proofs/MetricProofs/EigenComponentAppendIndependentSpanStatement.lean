module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenComponentAppendIndependentSpan
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
theorem _root_.GlobalTheory.T.eigenComponent_append_independent_span : ∀ (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : 𝓞 E →+* Module.End ℂ V) (s₀ : 𝓞 E →+* ℂ) (I₀ : AddSubgroup V) (r k : ℕ) (v : Fin r → V) (q : Fin k → V), IsOFamily ρ I₀ v → (∀ (c : 𝓞 E), ∀ x ∈ I₀, ρ c x ∈ I₀) → (∀ c, q c ∈ eigSp ρ s₀) → LinearIndependent ℂ (Fin.append (fun a => eigComp ρ s₀ (v a)) q) → ∀ l : Fin k → ℂ, ∑ c, l c • q c ∈ Submodule.span ℂ (I₀ : Set V) → l = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.EigIndep.eq_zero_of_sum_mem_span | exact GlobalTheory.CompanionTheory.Ar.Cusp.EigIndep.eq_zero_of_sum_mem_span | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.EigIndep.eq_zero_of_sum_mem_span <;> assumption)
