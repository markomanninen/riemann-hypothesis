module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartDensityChangeFormula
public import Development.AbelianVarietyTheory.Definitions.Divisors.ChartMeasApplyOfSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinateNearGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExists
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSchemeTheoreticallyDominantComplEffCartier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionOfDominantFlatCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Vert

namespace GlobalTheory.FlagChain

section Sub

variable {C C' : Type*} [Category C] [Category C'] {A B A' E E' : C}

variable {f : A ⟶ E} {g : B ⟶ E} {f' : A' ⟶ E}

end Sub

section Bundles

variable {X Y Z : Scheme.{0}} {A B E E' H : X.Modules} {r : ℕ}

end Bundles

section Covers

variable {k : Type} [CommRing k] {D : ℕ} {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  [IsIntegral Z] {p : X ⟶ Sp k} {A E L H : X.Modules} {r : ℕ}

def IsCov (p : X ⟶ Sp k) (D : ℕ) (ρ : Y ⟶ X) : Prop :=
  IsArithVar (ρ ≫ p) D ∧ ρ (genericPoint Y) = genericPoint X ∧ ρ.residueDegree (genericPoint Y) ≠ 0

end Covers

end GlobalTheory.FlagChain
