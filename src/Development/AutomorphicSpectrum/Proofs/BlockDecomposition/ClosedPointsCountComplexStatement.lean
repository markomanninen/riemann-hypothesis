module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedPointsCountComplex
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericResidueLinearIndependence
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodStalks

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_points_count_complex : ∀ (Y : Var ℂ) (Z : Set Y.X), (∀ x ∈ Z, IsClosed ({x} : Set Y.X)) → ({y : CxPts Y.str (RingHom.id ℂ) | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z}).ncard = Z.ncard := by
  first | exact @GlobalTheory.CompanionTheory.KoszulCount.ncard_cxPts_over_closed | exact GlobalTheory.CompanionTheory.KoszulCount.ncard_cxPts_over_closed | (intros; apply GlobalTheory.CompanionTheory.KoszulCount.ncard_cxPts_over_closed <;> assumption)
