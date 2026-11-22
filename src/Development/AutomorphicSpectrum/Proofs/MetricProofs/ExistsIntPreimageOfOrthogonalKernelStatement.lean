module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIntPreimageOfOrthogonalKernel
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
theorem _root_.GlobalTheory.T.exists_int_preimage_of_orthogonal_kernel : ∀ (g : ℕ) (S : Matrix (Fin g) (Fin g) ℤ), Sᵀ = S → ∀ u : Fin g → ℤ, (∀ v : Fin g → ℤ, S *ᵥ v = 0 → u ⬝ᵥ v = 0) → ∃ (N : ℤ) (c : Fin g → ℤ), N ≠ 0 ∧ N • u = S *ᵥ c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.IntegralKernel.exists_smul_eq_mulVec | exact GlobalTheory.CompanionTheory.Ar.IntegralKernel.exists_smul_eq_mulVec | (intros; apply GlobalTheory.CompanionTheory.Ar.IntegralKernel.exists_smul_eq_mulVec <;> assumption)
