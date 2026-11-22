module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
public import Development.WeilBound.CoreStatements.HodgeTatePoints.EqOfPowEqSelf

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem teichmuller_lift_of_embedding : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (F : Type) [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p] (ζ : O), IsPrimitiveRoot ζ (Fintype.card F - 1) → ∀ σ : F →+* IsLocalRing.ResidueField O, (∃! χ : F →*₀ O, ∀ a, IsLocalRing.residue O (χ a) = σ a) ∧ ∀ (σ' : F →+* IsLocalRing.ResidueField O) (χ χ' : F →*₀ O), (∀ a, σ' a = σ a ^ p) → (∀ a, IsLocalRing.residue O (χ a) = σ a) → (∀ a, IsLocalRing.residue O (χ' a) = σ' a) → ∀ a, χ' a = χ a ^ p :=
  PositivityTheory.HtPt.Teich.glue_teich

end GlobalTheory.CompanionTheory.Ar.Num
