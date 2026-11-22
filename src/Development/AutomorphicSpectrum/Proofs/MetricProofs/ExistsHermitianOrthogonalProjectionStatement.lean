module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsHermitianOrthogonalProjection
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.QuotientLatticeByIsotropicSubmoduleStatement

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitian_orthogonal_projection : ∀ (g k : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) → ∀ u : Fin k → Fin g → ℂ, LinearIndependent ℂ u → ∀ z : Fin g → ℂ, ∃ c : Fin k → ℂ, ∀ j, (z - ∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (u j) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PosFormProjection.exists_orthogonal_coefficients | exact GlobalTheory.CompanionTheory.Ar.PosFormProjection.exists_orthogonal_coefficients | (intros; apply GlobalTheory.CompanionTheory.Ar.PosFormProjection.exists_orthogonal_coefficients <;> assumption)
