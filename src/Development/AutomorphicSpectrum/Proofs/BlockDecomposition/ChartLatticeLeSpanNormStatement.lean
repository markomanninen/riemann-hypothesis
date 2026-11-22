module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeLeSpanNorm
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftSectionBound
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GeneratedModOfSubsingleton
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAmpleOfGenTwist
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AmpleSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lattice_le_span_norm : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ), chartLatQ y a τ ≤ Submodule.span ℚ (chartLatNm y a τ : Set Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartDenom.chartLatQ_le_span_chartLatNm | exact GlobalTheory.CompanionTheory.Ar.ChartDenom.chartLatQ_le_span_chartLatNm | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartDenom.chartLatQ_le_span_chartLatNm <;> assumption)
