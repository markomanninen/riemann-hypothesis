module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VarietyStalkRegularDim
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
theorem _root_.GlobalTheory.T.variety_stalk_regular_dim : ∀ (Y : Var ℂ) (x : Y.X), IsRegularLocalRing (Y.X.presheaf.stalk x) ∧ ringKrullDim (Y.X.presheaf.stalk x) ≤ Y.dim := by
  first | exact @GlobalTheory.CompanionTheory.KoszulCount.stalk_isRegularLocalRing_and_ringKrullDim_le | exact GlobalTheory.CompanionTheory.KoszulCount.stalk_isRegularLocalRing_and_ringKrullDim_le | (intros; apply GlobalTheory.CompanionTheory.KoszulCount.stalk_isRegularLocalRing_and_ringKrullDim_le <;> assumption)
