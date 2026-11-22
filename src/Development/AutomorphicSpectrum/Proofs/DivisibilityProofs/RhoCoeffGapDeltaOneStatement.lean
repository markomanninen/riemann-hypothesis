module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RhoCoeffGapDeltaOne
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rho_coeff_gap_delta_one : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ), AddMonoidAlgebra.coeff (gapDelta Ψ N) (rhoM Ψ N) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.FlDeg.coeff_rhoM_gapDelta | exact GlobalTheory.CompanionTheory.Ar.Top.FlDeg.coeff_rhoM_gapDelta | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.coeff_rhoM_gapDelta <;> assumption)
