module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDensityOfBallPotential
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monge_ampere_density_of_ball_potential : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n), ∃ c : ℝ, 0 < c ∧ ∀ t ∈ ballDom q, maDensity (fun (_ : Fin n) t' => ballPot q t' / 2) t = c * ballDens q t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BallHess.maDensity_half_ballPot | exact GlobalTheory.CompanionTheory.Ar.Cusp.BallHess.maDensity_half_ballPot | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BallHess.maDensity_half_ballPot <;> assumption)
