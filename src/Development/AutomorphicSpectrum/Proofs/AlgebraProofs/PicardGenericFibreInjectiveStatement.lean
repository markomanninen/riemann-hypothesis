module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PicardGenericFibreInjective
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
theorem _root_.GlobalTheory.T.picard_generic_fibre_injective : ∀ (C : Type) [Field C] [IsAlgClosed C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ Y : A.left.Opens, IsCompact (Y : Set A.left) →
    ∀ q : Pic Y.toScheme, pull (pullback.fst A.hom (spMap (algebraMap R C)) ∣_ Y) q = 0 → q = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ValFibre.eq_zero_of_pull_generic_eq_zero | exact GlobalTheory.CompanionTheory.ValFibre.eq_zero_of_pull_generic_eq_zero | (intros; apply GlobalTheory.CompanionTheory.ValFibre.eq_zero_of_pull_generic_eq_zero <;> assumption)
