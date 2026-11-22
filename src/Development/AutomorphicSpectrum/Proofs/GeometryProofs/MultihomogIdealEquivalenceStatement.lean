module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogIdealEquivalence
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence

@[expose] public section

open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMultiHomogIdeal_transfer : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal P → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.CompMem.comp_mem | exact GlobalTheory.CompanionTheory.Ggeo.CompMem.comp_mem | (intros; apply GlobalTheory.CompanionTheory.Ggeo.CompMem.comp_mem <;> assumption)
