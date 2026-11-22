module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimLeOfIsClosedNeUnivIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfForallIsPsEff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_le_of_isClosed_ne_univ_integral : ∀ (X : Scheme.{0}) [IsIntegral X] (d : ℕ), topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ Z : Set X, IsClosed Z → Z ≠ Set.univ → topologicalKrullDim Z ≤ (d : ℕ) := by
  first | exact @GlobalTheory.topologicalKrullDim_le_of_isClosed_ne_univ | exact GlobalTheory.topologicalKrullDim_le_of_isClosed_ne_univ | (intros; apply GlobalTheory.topologicalKrullDim_le_of_isClosed_ne_univ <;> assumption)
