module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SectionThroughClosedPoint
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearIsIsoOfIsProperOfFinitePresentation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFibres
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorExtendsFromGenericFibreValuationRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelExtensionOverDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymTranslate
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StrictModelTranslatesTwistCompatible
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_through_closed_point : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] (X : Over (Sp R)), Smooth X.hom →
    (∀ z : X.left, IsClosed {z} → X.hom z = IsLocalRing.closedPoint R →
      ∃ s : 𝟙_ (Over (Sp R)) ⟶ X, s.left (IsLocalRing.closedPoint R) = z) ∧
    (∀ U : X.left.Opens, (∃ z ∈ U, X.hom z = IsLocalRing.closedPoint R) →
      ∃ s : 𝟙_ (Over (Sp R)) ⟶ X, s.left (IsLocalRing.closedPoint R) ∈ U) := by
  first | exact @GlobalTheory.CompanionTheory.Sections.exists_section | exact GlobalTheory.CompanionTheory.Sections.exists_section | (intros; apply GlobalTheory.CompanionTheory.Sections.exists_section <;> assumption)
