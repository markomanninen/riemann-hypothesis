module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsEqOfSpMapSubtypeCompEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundleIsoDescendsToSubringOfFinset
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MorphismDescendsToSubring
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsNoethModel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrincipalObjectDescendsLargeSubfield
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_spMap_subtype_comp_eq_of_isSeparated : ∀ (R : Type) [CommRing R] (R₀ : Subring R) (X : Scheme.{0}) (p : X ⟶ Sp R₀) [IsSeparated p] (x y : Sp R₀ ⟶ X), x ≫ p = y ≫ p → spMap R₀.subtype ≫ x = spMap R₀.subtype ≫ y → x = y := by
  first | exact @GlobalTheory.sections_eq_of_spMap_subtype_comp_eq | exact GlobalTheory.sections_eq_of_spMap_subtype_comp_eq | (intros; apply GlobalTheory.sections_eq_of_spMap_subtype_comp_eq <;> assumption)
